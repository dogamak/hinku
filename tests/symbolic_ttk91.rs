use logos::{Lexer, Logos};

use hinku::{
    either, match_token, BufferedStream, Either, ParseError, ParseResult, ParseResultExt, Span,
    TokenStream, TokenStreamExt,
};

#[derive(Debug, Clone, PartialEq)]
enum Register {
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
}

fn register_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> std::result::Result<Register, ()> {
    match lex.slice() {
        "R1" => Ok(Register::R1),
        "R2" => Ok(Register::R2),
        "R3" => Ok(Register::R3),
        "R4" => Ok(Register::R4),
        "R5" => Ok(Register::R5),
        "R6" => Ok(Register::R6),
        "R7" | "SP" => Ok(Register::R7),
        _ => Err(()),
    }
}

#[derive(Debug, Clone, PartialEq)]
enum PseudoOpCode {
    DC,
    DS,
    EQU,
}

fn pseudo_operator_callback<'a>(
    lex: &mut Lexer<'a, Token<'a>>,
) -> std::result::Result<PseudoOpCode, ()> {
    match lex.slice().to_uppercase().as_ref() {
        "DC" => Ok(PseudoOpCode::DC),
        "DS" => Ok(PseudoOpCode::DS),
        "EQU" => Ok(PseudoOpCode::EQU),
        _ => Err(()),
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum JumpCondition {
    Unconditional,
    Positive,
    Negative,
    Zero,
    Equal,
    Less,
    Greater,
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum OpCode {
    NoOperation,
    Store,
    Load,
    In,
    Out,
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    And,
    Or,
    Xor,
    ShiftLeft,
    ShiftRight,
    Not,
    // ArithmeticShiftRight,
    Compare,
    Jump {
        condition: JumpCondition,
        negated: bool,
    },
    Call,
    Exit,
    Push,
    Pop,
    PushRegisters,
    PopRegisters,
    SupervisorCall,
}

fn operator_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> std::result::Result<OpCode, ()> {
    let opcode = match lex.slice().to_uppercase().as_ref() {
        "NOP" => OpCode::NoOperation,
        "STORE" => OpCode::Store,
        "LOAD" => OpCode::Load,
        "IN" => OpCode::In,
        "OUT" => OpCode::Out,
        "ADD" => OpCode::Add,
        "SUB" => OpCode::Subtract,
        "MUL" => OpCode::Multiply,
        "DIV" => OpCode::Divide,
        "MOD" => OpCode::Modulo,
        "AND" => OpCode::And,
        "OR" => OpCode::Or,
        "XOR" => OpCode::Xor,
        "SHL" => OpCode::ShiftLeft,
        "SHR" => OpCode::ShiftRight,
        "NOT" => OpCode::Not,
        "COMP" => OpCode::Compare,
        "CALL" => OpCode::Call,
        "EXIT" => OpCode::Exit,
        "PUSH" => OpCode::Push,
        "POP" => OpCode::Pop,
        "PUSHR" => OpCode::PushRegisters,
        "POPR" => OpCode::PopRegisters,
        "SVC" => OpCode::SupervisorCall,
        "JUMP" => OpCode::Jump {
            negated: false,
            condition: JumpCondition::Unconditional,
        },
        "JZER" => OpCode::Jump {
            negated: false,
            condition: JumpCondition::Zero,
        },
        "JNZER" => OpCode::Jump {
            negated: true,
            condition: JumpCondition::Zero,
        },
        "JPOS" => OpCode::Jump {
            negated: false,
            condition: JumpCondition::Positive,
        },
        "JNPOS" => OpCode::Jump {
            negated: true,
            condition: JumpCondition::Positive,
        },
        "JNEG" => OpCode::Jump {
            negated: false,
            condition: JumpCondition::Negative,
        },
        "JNNEG" => OpCode::Jump {
            negated: true,
            condition: JumpCondition::Negative,
        },
        "JEQU" => OpCode::Jump {
            negated: false,
            condition: JumpCondition::Equal,
        },
        "JNEQU" => OpCode::Jump {
            negated: true,
            condition: JumpCondition::Equal,
        },
        "JLES" => OpCode::Jump {
            negated: false,
            condition: JumpCondition::Less,
        },
        "JNLES" => OpCode::Jump {
            negated: true,
            condition: JumpCondition::Less,
        },
        "JGRE" => OpCode::Jump {
            negated: false,
            condition: JumpCondition::Greater,
        },
        "JNGRE" => OpCode::Jump {
            negated: true,
            condition: JumpCondition::Greater,
        },
        _ => return Err(()),
    };

    Ok(opcode)
}

#[derive(Logos, Debug, PartialEq, Clone)]
enum Token<'a> {
    #[error]
    #[regex(r"[ \n\t\f]", logos::skip)]
    #[regex(r";[^\n]*", logos::skip)]
    Error,

    #[regex("R[1-7]|SP|FP", register_callback)]
    Register(Register),

    #[regex("[A-Za-z][A-Za-z0-9_]*", Lexer::slice)]
    Symbol(&'a str),

    #[regex("(?i)nop|store|load|in|out|add|sub|mul|div|mod|and|or|xor|shl|shr|not|comp|call|exit|push|pop|pushr|popr|svc|jump|jzer|jnzer|jpos|jnpos|jneg|jnneg|jequ|jnequ|jles|jnles|jgre|jngre", operator_callback)]
    Operator(OpCode),

    #[regex("(?i)dc|ds|equ", pseudo_operator_callback)]
    PseudoOperator(PseudoOpCode),

    #[token("@")]
    IndirectModifier,

    #[token("=")]
    ImmediateModifier,

    #[token(",")]
    ParameterSeparator,

    #[token("(")]
    IndexBegin,

    #[token(")")]
    IndexEnd,

    #[regex("-?[0-9]+", |lex| lex.slice().parse())]
    Literal(i32),
}

#[derive(Debug, Clone, PartialEq)]
enum BaseOperand {
    Symbol(String),
    Literal(i32),
    Register(Register),
}

type Result<T> = ParseResult<T, String>;

fn symbol(stream: &mut dyn TokenStream<Token>) -> Result<String> {
    match_token!(stream, {
        Token::Symbol(sym) => Ok(sym.to_string()),
    })
    .expected("expected a symbol")
}

fn literal(stream: &mut dyn TokenStream<Token>) -> Result<i32> {
    match_token!(stream, {
        Token::Literal(num) => Ok(num),
    })
    .expected("expected a number literal")
}

fn register(stream: &mut dyn TokenStream<Token>) -> Result<Register> {
    match_token!(stream, {
        Token::Register(reg) => Ok(reg),
    })
    .expected("expected a register")
}

fn base_operand(mut stream: &mut dyn TokenStream<Token>) -> Result<BaseOperand> {
    let res = stream
        .take(either(symbol, either(literal, register)))
        .expected("expected a symbol, an integer literal or a register")?;

    match res {
        Either::Left(sym) => Ok(BaseOperand::Symbol(sym)),
        Either::Right(Either::Left(lit)) => Ok(BaseOperand::Literal(lit)),
        Either::Right(Either::Right(reg)) => Ok(BaseOperand::Register(reg)),
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Mode {
    Indirect,
    Direct,
    Immediate,
}

fn modifier(stream: &mut dyn TokenStream<Token>) -> Result<Mode> {
    match_token!(stream, {
        Token::IndirectModifier => Ok(Mode::Indirect),
        Token::ImmediateModifier => Ok(Mode::Immediate),
    })
    .expected("expected @ or =")
}

fn index_register(mut stream: &mut dyn TokenStream<Token>) -> Result<Option<Register>> {
    if stream.assert_token(Token::IndexBegin).is_ok() {
        stream.commit();
        let reg = stream.take(register)?;
        stream
            .assert_token(Token::IndexEnd)
            .expected("expected a closing parenthesis")?;
        return Ok(Some(reg));
    }

    Ok(None)
}

#[derive(Debug, Clone, PartialEq)]
struct SecondOperand {
    mode: Mode,
    base: BaseOperand,
    index: Option<Register>,
}

fn second_operand(mut stream: &mut dyn TokenStream<Token>) -> Result<SecondOperand> {
    let mode = stream.take(modifier).optional().unwrap_or(Mode::Direct);
    let base = stream.take(base_operand)?;
    let index = index_register(stream)?;

    Ok(SecondOperand { mode, base, index })
}

fn concrete_opcode(stream: &mut dyn TokenStream<Token>) -> Result<OpCode> {
    match_token!(stream, {
        Token::Operator(op) => Ok(op),
    })
    .expected("expected a opcode")
}

fn pseudo_opcode(stream: &mut dyn TokenStream<Token>) -> Result<PseudoOpCode> {
    match_token!(stream, {
        Token::PseudoOperator(op) => Ok(op),
    })
    .expected("expected a opcode")
}

#[derive(Debug, Clone, PartialEq)]
struct ConcreteInstruction {
    op: OpCode,
    operand1: Register,
    operand2: SecondOperand,
}

fn concrete_instruction(mut stream: &mut dyn TokenStream<Token>) -> Result<ConcreteInstruction> {
    let op = stream.take(concrete_opcode)?;

    if op == OpCode::NoOperation {
        return Ok(ConcreteInstruction {
            op: OpCode::NoOperation,
            operand1: Register::R1,
            operand2: SecondOperand {
                mode: Mode::Immediate,
                base: BaseOperand::Literal(0),
                index: None,
            },
        });
    }

    if let OpCode::Jump {
        condition: JumpCondition::Unconditional,
        negated: false,
    } = op
    {
        let operand2 = stream.take(second_operand)?;

        return Ok(ConcreteInstruction {
            op,
            operand1: Register::R7,
            operand2,
        });
    }

    let operand1 = stream.take(register)?;

    if let OpCode::PushRegisters | OpCode::PopRegisters | OpCode::Not = op {
        return Ok(ConcreteInstruction {
            op,
            operand1,
            operand2: SecondOperand {
                mode: Mode::Immediate,
                base: BaseOperand::Literal(0),
                index: None,
            },
        });
    }

    stream
        .assert_token(Token::ParameterSeparator)
        .expected("expected a comma")?;

    Ok(ConcreteInstruction {
        op,
        operand1,
        operand2: stream.take(second_operand)?,
    })
}

#[derive(Debug, Clone, PartialEq)]
struct PseudoInstruction {
    op: PseudoOpCode,
    operand: i32,
}

fn pseudo_instruction(mut stream: &mut dyn TokenStream<Token>) -> Result<PseudoInstruction> {
    let op = stream.take(pseudo_opcode)?;
    let operand = stream.take(literal)?;

    Ok(PseudoInstruction { op, operand })
}

#[derive(Debug, Clone, PartialEq)]
enum Instruction {
    Concrete(ConcreteInstruction),
    Pseudo(PseudoInstruction),
}

fn instruction(mut stream: &mut dyn TokenStream<Token>) -> Result<Instruction> {
    let res = stream
        .take(either(pseudo_instruction, concrete_instruction))
        .expected("invalid instruction")?;

    match res {
        Either::Left(pseudo) => Ok(Instruction::Pseudo(pseudo)),
        Either::Right(concrete) => Ok(Instruction::Concrete(concrete)),
    }
}

fn program(mut stream: &mut dyn TokenStream<Token>) -> Result<Vec<(Vec<String>, Instruction)>> {
    let mut program = Vec::new();

    loop {
        let mut labels = Vec::new();

        while let Some(label) = stream.take(symbol).optional() {
            labels.push(label);
        }

        let instruction = match stream.take(instruction) {
            Ok(ins) => ins,
            Err(ParseError::EndOfStream) => break,
            Err(err) => return Err(err),
        };

        program.push((labels, instruction));
    }

    Ok(program)
}

fn calculate_position(input: &str, span: &Span) -> (usize, usize) {
    input[..span.start]
        .split('\n')
        .fold((0, 0), |(line_nr, _column), line| (line_nr + 1, line.len()))
}

#[test]
fn sum() {
    let input = r#"
; sum - laske annettuja lukuja yhteen kunnes nolla annettu

Luku  DC    0           ; nykyinen luku
Summa DC    0           ; nykyinen summa

Sum   IN    R1, =KBD	; ohjelma alkaa käskystä 0
      STORE R1, Luku
      JZER  R1, Done    ; luvut loppu?
	
      LOAD  R1, Summa   ; Summa <- Summa+Luku
      ADD   R1, Luku	
      STORE R1, Summa   ; summa muuttujassa, ei rekisterissa?

      JUMP  Sum

Done  LOAD  R1, Summa(R2)   ; tulosta summa ja lopeta
      OUT   R1, =CRT

      SVC   SP, =HALT
    "#;

    let lex = Token::lexer(input);

    let mut stream = BufferedStream::new(lex.spanned());

    let program = stream.take(program);

    assert_eq!(
        program,
        Ok(vec![
            (
                vec!["Luku".into()],
                Instruction::Pseudo(PseudoInstruction {
                    op: PseudoOpCode::DC,
                    operand: 0
                })
            ),
            (
                vec!["Summa".into()],
                Instruction::Pseudo(PseudoInstruction {
                    op: PseudoOpCode::DC,
                    operand: 0
                })
            ),
            (
                vec!["Sum".into()],
                Instruction::Concrete(ConcreteInstruction {
                    op: OpCode::In,
                    operand1: Register::R1,
                    operand2: SecondOperand {
                        mode: Mode::Immediate,
                        base: BaseOperand::Symbol("KBD".into()),
                        index: None
                    }
                })
            ),
            (
                vec![],
                Instruction::Concrete(ConcreteInstruction {
                    op: OpCode::Store,
                    operand1: Register::R1,
                    operand2: SecondOperand {
                        mode: Mode::Direct,
                        base: BaseOperand::Symbol("Luku".into()),
                        index: None
                    }
                })
            ),
            (
                vec![],
                Instruction::Concrete(ConcreteInstruction {
                    op: OpCode::Jump {
                        condition: JumpCondition::Zero,
                        negated: false
                    },
                    operand1: Register::R1,
                    operand2: SecondOperand {
                        mode: Mode::Direct,
                        base: BaseOperand::Symbol("Done".into()),
                        index: None
                    }
                })
            ),
            (
                vec![],
                Instruction::Concrete(ConcreteInstruction {
                    op: OpCode::Load,
                    operand1: Register::R1,
                    operand2: SecondOperand {
                        mode: Mode::Direct,
                        base: BaseOperand::Symbol("Summa".into()),
                        index: None
                    }
                })
            ),
            (
                vec![],
                Instruction::Concrete(ConcreteInstruction {
                    op: OpCode::Add,
                    operand1: Register::R1,
                    operand2: SecondOperand {
                        mode: Mode::Direct,
                        base: BaseOperand::Symbol("Luku".into()),
                        index: None
                    }
                })
            ),
            (
                vec![],
                Instruction::Concrete(ConcreteInstruction {
                    op: OpCode::Store,
                    operand1: Register::R1,
                    operand2: SecondOperand {
                        mode: Mode::Direct,
                        base: BaseOperand::Symbol("Summa".into()),
                        index: None
                    }
                })
            ),
            (
                vec![],
                Instruction::Concrete(ConcreteInstruction {
                    op: OpCode::Jump {
                        condition: JumpCondition::Unconditional,
                        negated: false
                    },
                    operand1: Register::R7,
                    operand2: SecondOperand {
                        mode: Mode::Direct,
                        base: BaseOperand::Symbol("Sum".into()),
                        index: None
                    }
                })
            ),
            (
                vec!["Done".into()],
                Instruction::Concrete(ConcreteInstruction {
                    op: OpCode::Load,
                    operand1: Register::R1,
                    operand2: SecondOperand {
                        mode: Mode::Direct,
                        base: BaseOperand::Symbol("Summa".into()),
                        index: Some(Register::R2),
                    }
                })
            ),
            (
                vec![],
                Instruction::Concrete(ConcreteInstruction {
                    op: OpCode::Out,
                    operand1: Register::R1,
                    operand2: SecondOperand {
                        mode: Mode::Immediate,
                        base: BaseOperand::Symbol("CRT".into()),
                        index: None
                    }
                })
            ),
            (
                vec![],
                Instruction::Concrete(ConcreteInstruction {
                    op: OpCode::SupervisorCall,
                    operand1: Register::R7,
                    operand2: SecondOperand {
                        mode: Mode::Immediate,
                        base: BaseOperand::Symbol("HALT".into()),
                        index: None
                    }
                })
            ),
        ])
    );

    // println!("{:?}", program);

    let span;
    let error;

    match program {
        Err(ParseError::UnexpectedToken { span: s }) => {
            span = s;
            error = "unexpected token".to_string();
        }
        Err(ParseError::Custom {
            span: s,
            error: mut e,
        }) => {
            span = s;
            e.reverse();
            error = e.join(": ");
        }
        _ => return,
    }

    let (line_nr, column) = calculate_position(input, &span);
    let line_orig = input.lines().skip(line_nr - 1).next().unwrap();

    let line = line_orig.trim();

    let prefix = format!("Line {}: Error: ", line_nr);

    println!("{}{}", prefix, line);

    for _ in 0..column + prefix.len() - (line_orig.len() - line.len()) {
        print!(" ");
    }

    for _ in 0..span.end - span.start {
        print!("^");
    }

    println!(" {}", error);
}
