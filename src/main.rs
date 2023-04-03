use anyhow::{anyhow, Result};
use clap::{Parser, Subcommand};
use serde::Deserialize;
use std::fs::File;
use std::io::{Read, Write};
use std::path::PathBuf;

static MAX_REG: usize = 0xFF;

#[derive(Parser, Debug)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    Compile {
        source: PathBuf,

        #[arg(short, long)]
        out: Option<PathBuf>,
    },

    Debug {
        source: PathBuf,

        #[arg(short, long)]
        out: Option<PathBuf>,
    },
}

#[derive(Debug)]
enum Operand {
    None,
    Register(usize),
    Memory(usize),

    // Static Values
    Constant(usize),
    Relative(isize),
    Label(String),
}

impl Operand {
    fn parse(s: &str) -> Result<Self> {
        Ok(
            match s
                .chars()
                .nth(0)
                .ok_or(anyhow!("Opcode has a length of 0: {}", s))?
            {
                '$' | 'R' => Self::Register(
                    s.get(1..)
                        .ok_or(anyhow!("Unable to determine register number: {}", s))?
                        .parse::<usize>()?,
                ),
                '#' | 'M' => Self::Memory(
                    s.get(1..)
                        .ok_or(anyhow!("Unable to determine memory address: {}", s))?
                        .parse::<usize>()?,
                ),
                '0' => match s.chars().nth(1) {
                    Some(c) => match c {
                        'b' => Self::Constant(usize::from_str_radix(
                            s.get(2..)
                                .ok_or(anyhow!("Unable to determine binary value: {}", s))?,
                            2,
                        )?),
                        'x' => Self::Constant(usize::from_str_radix(
                            s.get(2..)
                                .ok_or(anyhow!("Unable to determine hex value: {}", s))?,
                            16,
                        )?),
                        _ => Err(anyhow!("Unable to determine number type: {}", s))?,
                    },
                    None => Self::Constant(0),
                },
                '1'..='9' => Self::Constant(s.parse::<usize>()?),
                '~' => Self::Relative(
                    match s
                        .chars()
                        .nth(1)
                        .ok_or(anyhow!("Malformed Relative {}", s))?
                    {
                        '+' => 1,
                        '-' => -1,
                        _ => Err(anyhow!("Invalid Sign"))?,
                    } * s
                        .get(2..)
                        .ok_or(anyhow!("Relative, no number: {}", s))?
                        .parse::<isize>()?,
                ),
                '.' => Self::Label(String::from(
                    s.get(1..).ok_or(anyhow!("Empty Label operand: {}", s))?,
                )),
                _ => Err(anyhow!("Unable to determine: {}", s))?,
            },
        )
    }

    fn to_string(&self) -> Result<String> {
        Ok(match self {
            Self::Constant(a) => a.to_string(),
            Self::Label(s) => format!(".{}", s),
            Self::Memory(a) => format!("M{}", a),
            Self::Register(a) => format!("R{}", a),
            Self::Relative(a) => format!("~{}{}", if a > &0 { '+' } else { '-' }, a.abs()),
            Self::None => String::new(),
        })
    }
}

#[derive(Debug)]
struct Instruction {
    opcode: String,
    dst: Operand,
    src1: Operand,
    src2: Operand,
}

impl Instruction {
    fn parse(s: &str) -> Result<Self> {
        let (opcode, operands) = s
            .split_once(" ")
            .ok_or(anyhow!("Unable to seperate opcode from operands: {}", s))?;

        let (dst, srcs) = match operands.split_once(" ") {
            Some((dst, srcs)) => (dst, Some(srcs)),
            None => (operands, None),
        };

        let (src1, src2) = match srcs {
            Some(srcs) => match srcs.split_once(" ") {
                Some((src1, src2)) => (Some(src1), Some(src2)),
                None => (Some(srcs), None),
            },
            None => (None, None),
        };

        Ok(Self {
            opcode: String::from(opcode).to_lowercase(),
            dst: Operand::parse(dst)?,
            src1: match src1 {
                Some(operand) => Operand::parse(operand)?,
                None => Operand::None,
            },
            src2: match src2 {
                Some(operand) => Operand::parse(operand)?,
                None => Operand::None,
            },
        })
    }

    fn to_string(&self) -> Result<String> {
        let mut buf = format!("{} {}", self.opcode, self.dst.to_string()?);

        buf += match self.src1 {
            Operand::None => String::new(),
            _ => format!(" {}", self.src1.to_string()?),
        }
        .as_str();
        buf += match self.src2 {
            Operand::None => String::new(),
            _ => format!(" {}", self.src2.to_string()?),
        }
        .as_str();

        Ok(buf)
    }
}

#[derive(Debug)]
enum Line {
    Comment(String),
    Label(String),
    Instruction(Instruction),
    Empty,
}

impl Line {
    fn parse(s: &str) -> Result<Self> {
        Ok(match s.chars().nth(0) {
            Some(c) => match c {
                '/' => Self::Comment(String::from(s.get(2..).unwrap_or(""))),
                '.' => Self::Label(String::from(
                    s.get(1..).ok_or(anyhow!("Empty label: {}", s))?,
                )),
                _ => Self::Instruction(Instruction::parse(s)?),
            },
            None => Self::Empty,
        })
    }

    fn to_string(&self) -> Result<String> {
        Ok(match self {
            Self::Comment(s) => format!("//{}", s),
            Self::Empty => String::new(),
            Self::Label(s) => format!(".{}", s),
            Self::Instruction(a) => a.to_string()?,
        })
    }
}

#[derive(Debug, Deserialize)]
enum SpecOperand {
    Constant,
    Register,
    Memory,
    None,
}

#[derive(Debug, Deserialize)]
struct Spec {
    opcode: String,
    dst: SpecOperand,
    src1: SpecOperand,
    src2: SpecOperand,
    translation: String,
}

#[derive(Debug, Deserialize)]
struct SpecFile {
    all: Vec<Spec>,
}

impl SpecFile {
    fn check_instruction(spec: &Spec, instruction: &Instruction) -> Result<bool> {
        Ok(match spec.dst {
            SpecOperand::Constant => match instruction.dst {
                Operand::Constant(_) => true,
                Operand::Label(_) => true,
                Operand::Relative(_) => true,
                _ => false,
            },
            SpecOperand::None => match instruction.dst {
                Operand::None => true,
                _ => false,
            },
            SpecOperand::Memory => match instruction.dst {
                Operand::Memory(_) => true,
                _ => false,
            },
            SpecOperand::Register => match instruction.dst {
                Operand::Register(_) => true,
                _ => false,
            },
        } && match spec.src1 {
            SpecOperand::Constant => match instruction.src1 {
                Operand::Constant(_) => true,
                Operand::Label(_) => true,
                Operand::Relative(_) => true,
                _ => false,
            },
            SpecOperand::None => match instruction.src1 {
                Operand::None => true,
                _ => false,
            },
            SpecOperand::Memory => match instruction.src1 {
                Operand::Memory(_) => true,
                _ => false,
            },
            SpecOperand::Register => match instruction.src1 {
                Operand::Register(_) => true,
                _ => false,
            },
        } && match spec.src2 {
            SpecOperand::Constant => match instruction.src2 {
                Operand::Constant(_) => true,
                Operand::Label(_) => true,
                Operand::Relative(_) => true,
                _ => false,
            },
            SpecOperand::None => match instruction.src2 {
                Operand::None => true,
                _ => false,
            },
            SpecOperand::Memory => match instruction.src2 {
                Operand::Memory(_) => true,
                _ => false,
            },
            SpecOperand::Register => match instruction.src2 {
                Operand::Register(_) => true,
                _ => false,
            },
        })
    }

    fn parse_line(&self, line: &Line, layer: usize) -> Result<String> {
        Ok(match line {
            Line::Instruction(instruction) => {
                let mut template: Option<String> = None;

                let specs = &self.all;
                for spec in specs
                    .into_iter()
                    .filter(|spec| spec.opcode == instruction.opcode)
                {
                    if Self::check_instruction(spec, &instruction)? {
                        template = Some(spec.translation.clone().trim().to_string());
                        break;
                    }
                }

                match template {
                    Some(s) => format!(
                        "// BEGIN: {0}\n{1}\n// END: {0}",
                        instruction.to_string()?,
                        s.replace("{a}", &instruction.dst.to_string()?)
                            .replace("{b}", &instruction.src1.to_string()?)
                            .replace("{c}", &instruction.src2.to_string()?)
                            .replace("{1}", &format!("R{}", MAX_REG - layer))
                            .replace("{2}", &format!("R{}", MAX_REG - layer - 1))
                            .replace("{3}", &format!("R{}", MAX_REG - layer - 2)),
                    ),
                    None => instruction.to_string()?,
                }
            }
            _ => line.to_string()?,
        })
    }
}

fn compile_parse(s: String) -> Result<Vec<Line>> {
    s.lines().map(|line| Line::parse(line.trim())).collect()
}

fn compile_debug(s: String) -> Result<String> {
    let lines = compile_parse(s)?;
    Ok(lines
        .into_iter()
        .fold(String::new(), |buf, line| format!("{}{:?}\n", buf, line)))
}

fn compile(s: String) -> Result<String> {
    let spec = toml::from_str::<SpecFile>(include_str!("../spec.toml"))?;
    let mut lines: Vec<(Line, usize)> = compile_parse(s)?
        .into_iter()
        .map(|line| (line, 0))
        .collect();

    for _ in 0x0..=0xFF {
        let mut parsed = Vec::new();

        for (line, layer) in &lines {
            parsed.append(
                &mut compile_parse(spec.parse_line(line, *layer)?)?
                    .into_iter()
                    .map(|line| (line, layer + 3))
                    .collect(),
            )
        }

        lines = parsed;
    }

    Ok(lines
        .into_iter()
        .fold(Ok(String::new()), |buf: Result<String>, (line, _)| {
            Ok(format!("{}{}\n", buf?, line.to_string()?))
        })?)
}

fn result_helper<F: Fn(String) -> Result<String>>(
    f: F,
    source: PathBuf,
    out: Option<PathBuf>,
) -> Result<()> {
    let mut file = File::open(&source)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    let out_path = match out {
        Some(path) => path,
        None => {
            let mut path = source.clone();
            path.set_file_name("a.urcl");
            path
        }
    };

    let result = f(contents)?;
    let mut out_file = File::create(out_path)?;
    out_file.write_all(result.as_bytes())?;

    Ok(())
}

fn main() -> Result<()> {
    let args = Args::parse();

    match args.command {
        Commands::Compile { source, out } => result_helper(compile, source, out),
        Commands::Debug { source, out } => result_helper(compile_debug, source, out),
    }?;

    Ok(())
}
