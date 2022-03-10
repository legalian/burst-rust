use nom::bytes::complete::{tag,take_while1,is_not,take};
use nom::character::{is_alphanumeric,is_digit/*,is_newline,is_space,*/};
use nom::character::complete::{multispace1/*,satisfy,none_of*/};
use nom::combinator::{map,recognize,not,/*map_opt,peek,success*/};
use nom::multi::{separated_list0,separated_list1,many0,many1};
use nom::sequence::{tuple,preceded,terminated,delimited};
use nom::combinator::all_consuming;
use nom::branch::alt;
use nom::combinator::{opt,map_res};
use nom::IResult;
use nom::character::complete::one_of;


fn commentful_multispace(ma: &str) -> IResult<&str,&str> {
    recognize(many0(
        alt((
            multispace1,
            recognize(delimited(
                white_tag("(*"),
                tuple((
                    is_not("*"),
                    many0(tuple((not(tag("*)")),take(1usize),is_not("*"))))
                )),
                white_tag("*)")
            ))
        ))
    ))(ma)
}

fn white_tag<'a>(ma: &'static str) -> impl FnMut(&'a str) -> IResult<&'a str, &'a str> {terminated(tag(ma),commentful_multispace)}
fn wrapper_parse<'a,T>(
	start: &'static str,end: &'static str,
	parser:impl FnMut(&'a str) -> IResult<&'a str, T>
) -> impl FnMut(&'a str) -> IResult<&'a str, T> {
	delimited(white_tag(start),parser,white_tag(end))
}
fn comma_delimt<'a,T>(
	start: &'static str,end: &'static str,
	jop:impl FnMut(&'a str) -> IResult<&'a str, T>
) -> impl FnMut(&'a str) -> IResult<&'a str, Vec<T>> {
	wrapper_parse(start,end,separated_list0(white_tag(","),jop))
}
fn prepipe_delimited<'a,T>(
	jop:impl FnMut(&'a str) -> IResult<&'a str, T>
) -> impl FnMut(&'a str) -> IResult<&'a str, Vec<T>> {
	many0(preceded(white_tag("|"),jop))
}

fn number(ma: &str) -> IResult<&str, usize> {map_res(take_while1(|chr:char|chr.is_ascii() && is_digit(chr as u8)),str::parse)(ma)}
fn padnumber(ma: &str) -> IResult<&str, usize> {terminated(number,commentful_multispace)(ma)}
fn symbol(ma: &str) -> IResult<&str, &str> {preceded(
    tuple((
        not(terminated(tag("with"),one_of(" \t\n"))),
        not(terminated(tag("equiv"),one_of(" \t\n")))
    )),
    take_while1(|chr:char|chr.is_ascii() && is_alphanumeric(chr as u8) || chr=='_'))(ma)}
fn padsymbol(ma: &str) -> IResult<&str, &str> {terminated(symbol,commentful_multispace)(ma)}


pub enum Type<'a> {
    StarType(Vec<Type<'a>>),
    ArrowType(Box<Type<'a>>,Box<Type<'a>>),
    IdentType(&'a str)
}
use Type::{*};
fn type_parser<'a>(input: &'a str) -> IResult<&'a str,Type<'a>> {
    map(separated_list1(
        white_tag("*"),
        map(tuple((
            alt((
                delimited(white_tag("("),type_parser,white_tag(")")),
                map(padsymbol,|x|IdentType(x))
            )),
            opt(preceded(white_tag("->"),type_parser))
        )),|(x,y)|match y {
            None=>x,
            Some(y)=>ArrowType(Box::new(x),Box::new(y))
        })
    ),|mut u|if u.len()==1 {u.remove(0)} else {StarType(u)})(input)
}

fn inner_type_parser<'a>(input: &'a str) -> IResult<&'a str,Type<'a>> {
    map(tuple((
        alt((
            map(delimited(white_tag("("),separated_list1(
                white_tag("*"),inner_type_parser),white_tag(")")),|mut u|if u.len()==1 {u.remove(0)} else {StarType(u)}),
            map(padsymbol,|x|IdentType(x))
        )),
        opt(preceded(white_tag("->"),inner_type_parser))
    )),|(x,y)|match y {
        None=>x,
        Some(y)=>ArrowType(Box::new(x),Box::new(y))
    })(input)
}

pub enum Value<'a> {
    NumericValue(usize),
    IdentValue(&'a str),
    AppValue(Vec<Value<'a>>),
    TupleValue(Vec<Value<'a>>)
}
use Value::{*};
fn value_parser<'a>(input: &'a str) -> IResult<&'a str,Value<'a>> {
    map(many1(
        alt((
            map(padnumber,|x|NumericValue(x)),
            map(padsymbol,|x|IdentValue(x)),
            map(comma_delimt("(",")",value_parser),|mut x|if x.len()==1 {x.remove(0)} else {TupleValue(x)}),
        ))
    ),
    // |x|x.into_iter().reduce(|x,y|AppValue(Box::new(x),Box::new(y))).unwrap()
    |mut x|if x.len()==1 {x.remove(0)} else {AppValue(x)}
    )(input)
}

pub enum Program<'a> {
    AppProg(Vec<Program<'a>>),
    TupleProg(Vec<Program<'a>>),
    FixpointProg(&'a str,Type<'a>,Box<Program<'a>>),
    MatchProg(Box<Program<'a>>,Vec<(Value<'a>,Program<'a>)>),
    FunProg(&'a str,Type<'a>,Box<Program<'a>>),
    NumericProg(usize),
    IdentProg(&'a str),
    ComparisonProg(Box<Program<'a>>,Box<Program<'a>>),
    NegComparisonProg(Box<Program<'a>>,Box<Program<'a>>),
    AccProg(Box<Program<'a>>,usize)
}
use Program::{*};
fn program_parser<'a>(input: &'a str) -> IResult<&'a str,Program<'a>> {
    map(many1(tuple((
        map(tuple((
            alt((
                map(comma_delimt("(",")",program_parser),|mut x|if x.len()==1 {x.remove(0)} else {TupleProg(x)}),
                map(preceded(white_tag("fix"),tuple((
                    preceded(white_tag("("), padsymbol),
                    delimited(white_tag(":"), type_parser, white_tag(")")),
                    preceded(white_tag("="), program_parser)
                ))),|(x,y,z)|FixpointProg(x,y,Box::new(z))),
                map(preceded(white_tag("match"),tuple((
                    program_parser,
                    preceded(white_tag("with"),prepipe_delimited(tuple((
                        value_parser,
                        preceded(white_tag("->"),program_parser)
                    ))))
                ))),|(x,y)|MatchProg(Box::new(x),y)),
                map(preceded(white_tag("fun"),tuple((
                    preceded(white_tag("("), padsymbol),
                    delimited(white_tag(":"), type_parser, white_tag(")")),
                    preceded(white_tag("->"), program_parser)
                ))),|(x,y,z)|FunProg(x,y,Box::new(z))),
                map(padnumber,|x|NumericProg(x)),
                map(padsymbol,|x|IdentProg(x))
            )),
            opt(preceded(white_tag("."),separated_list1(white_tag("."),padnumber)))
        )),|(x,y)|match y{
            None=>x,
            Some(y)=>y.into_iter().fold(x,|x,y|AccProg(Box::new(x),y))
        })
    ,opt(tuple((alt((map(white_tag("=="),|_|true),map(white_tag("!="),|_|false))),program_parser)))
    ))),|mut x|if x.len()==1 {
        match x.remove(0) {
            (x,None) => x,
            (x,Some((z,y))) => if z {ComparisonProg(Box::new(x),Box::new(y))} else {NegComparisonProg(Box::new(x),Box::new(y))}
        }
    } else {
        AppProg(x.into_iter().map(|(x,y)|{if !y.is_none() {panic!("AAAA")};x}).collect())
        // x.into_iter().map(|(x,y)|{if !y.is_none() {panic!("AAAA")};x}).reduce(|x,y|AppProg(Box::new(x),Box::new(y))).unwrap()
    })(input)
}
#[derive(Debug)]
pub enum Line<'a> {
    IncludeLine(&'a str),
    LetLine(&'a str,Program<'a>),
    TypeLine(&'a str,Vec<(&'a str,Vec<Type<'a>>)>),
}
use Line::{*};
pub fn line_parser<'a>(input: &'a str) -> IResult<&'a str,Line<'a>> {
    alt((
        map(delimited(white_tag("include"),delimited(
            tag("\""),is_not("\""),tag("\"")
        ),commentful_multispace),|x|IncludeLine(x)),
        map(delimited(white_tag("let"),tuple((
            padsymbol,
            preceded(white_tag("="),program_parser))
        ),white_tag(";;")),|(x,y)|LetLine(x,y)),
        map(preceded(white_tag("type"),tuple((
            padsymbol,
            preceded(white_tag("="),prepipe_delimited(tuple((
                padsymbol,
                map(opt(preceded(white_tag("of"), separated_list1(
                    white_tag("*"), inner_type_parser) )),|u|u.unwrap_or_default())
            ))))
        ))),|(x,y)|TypeLine(x,y))
    ))(input)
}


#[derive(Debug)]
pub enum SpecType<'a> {
    IOSpec(Vec<(Vec<Program<'a>>,Program<'a>)>),
    LogicalSpec(Program<'a>),
    RefSpec(Program<'a>),
}
use SpecType::{*};
#[derive(Debug)]
pub struct SpecObj<'a> {
    pub earlier_lines:Vec<Line<'a>>,
    pub synth_type:Type<'a>,
    pub spec_type:SpecType<'a>
}
pub fn decls_parser<'a>(input: &'a str) -> IResult<&'a str,Vec<Line<'a>>> {
    all_consuming(preceded(commentful_multispace,many0(line_parser)))(input)
}
pub fn spec_parser<'a>(input: &'a str) -> IResult<&'a str,SpecObj<'a>> {
    all_consuming(preceded(commentful_multispace,
        map(tuple((
            many0(line_parser),
            delimited(white_tag("synth"),type_parser,white_tag("satisfying")),
            many0(line_parser),
            alt((
                map(terminated(separated_list1(white_tag(","),tuple((
                    comma_delimt("[","]",program_parser),
                    preceded(white_tag("->"),program_parser)
                ))),opt(white_tag(","))),|x|IOSpec(x)),
                map(preceded(white_tag("equiv"),program_parser),|y|RefSpec(y)),
                map(program_parser,|y|LogicalSpec(y)),
            ))
        )),|(x,y,z,w)|
            SpecObj{earlier_lines:x.into_iter().chain(z.into_iter()).collect(),synth_type:y,spec_type:w}
        )
    ))(input)
}
