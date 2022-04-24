

use crate::dsl::{Dsl,ExpressionContext};
use crate::mlsparser::{Program,Value,Type};
use crate::nftabuilder::{ExpressionBuilder,ProcType,ProcValue};
use crate::nfta::{PartialNFTA,NFTABuilder,Transition};
use std::fmt::Write;
use core::fmt::{Debug,Formatter,Error};
use std::collections::HashMap;
use std::collections::VecDeque;
use std::collections::hash_map::Entry::*;
use std::collections::HashSet;
use std::rc::Rc;
use Dsl::{*};
use Program::{*};
use Value::{*};
use Type::{*};
use ProcType::{*};
use ProcValue::{*};
use Transition::{*};


impl<T:Debug> NFTABuilder<T> {
    pub fn count_relevant_states(&self,a:usize) {
        let mut relevant = HashSet::new();
        let mut stack = vec![a];
        while let Some(a) = stack.pop() {
            if !relevant.insert(a) {continue;}
            for (_,row) in self.paths[a].0.iter() {
                stack.extend(row.iter().copied());
            }
        }
        println!("relevant states: {}",relevant.len());
    }
    pub fn output_tree(&self,a:usize)->Result<(),Error> {
        let mut relevant = HashMap::new();
        relevant.insert(a,0);
        relevant.insert(0,999);
        let mut index = 1;
        let mut queue = VecDeque::new();
        queue.push_back((a,0));
        let mut buffer = String::new();
        while let Some((a,iu)) = queue.pop_front() {
            if iu != 0 {buffer.write_char(',')?;}
            for (iu,(f,row)) in self.paths[a].0.iter().enumerate() {
                if iu != 0 {buffer.write_char('|')?;}
                match f {
                    // Constant(_)=>buffer.write_str("const"),
                    // Input=>buffer.write_str("input"),
                    // Destruct(_,_)=>buffer.write_str("destruct"),
                    // Transition::Construct(_)=>buffer.write_str("construct"),
                    // Switch(_)=>buffer.write_str("switch"),
                    // Recursion=>buffer.write_str("recursion"),
                    // ArbitraryFunc(_)=>buffer.write_str("func")
                    // Constant(x)=>buffer.write_fmt(format_args!("const[{:?}]",x)),
                    Input=>buffer.write_str("input"),
                    Destruct(c,i)=>buffer.write_fmt(format_args!("destruct[{},{}]",c,i)),
                    Transition::Construct(c)=>buffer.write_fmt(format_args!("construct[{}]",c)),
                    Switch(w)=>buffer.write_fmt(format_args!("switch[{}]",w)),
                    Recursion=>buffer.write_str("recursion"),
                    ArbitraryFunc(w)=>buffer.write_fmt(format_args!("func[{}]",w))
                }?;
                buffer.write_char('(')?;
                for (iu,r) in row.iter().enumerate() {
                    if iu != 0 {buffer.write_char(',')?;}
                    let ii = match relevant.entry(*r) {
                        Occupied(x)=>{*x.get()}
                        Vacant(x)=>{x.insert(index);queue.push_back((*r,index));index+=1;index-1}
                    };
                    buffer.write_fmt(format_args!("{}",ii))?;
                }
                buffer.write_char(')')?;
            }
        }
        println!("FTA: {}",buffer);
        Ok(())
    }
}

struct DebugNFTAline<'a,T:Debug> {
    token:Transition,
    arglist:&'a Vec<T>,
    fin:T,
    expr:&'a ExpressionBuilder
}
impl<'a,T:Debug> Debug for DebugNFTAline<'a,T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match self.token {
            // Constant(x)=>f.write_fmt(format_args!("const[{:?}]",DebugValue{t:x,expr:self.expr})),
            Input=>f.write_str("input"),
            Destruct(c,i)=>f.write_fmt(format_args!("destruct[{},{}]",c,i)),
            Transition::Construct(c)=>f.write_fmt(format_args!("construct[{}]",c)),
            Switch(_)=>f.write_str("switch"),
            Recursion=>f.write_str("recursion"),
            ArbitraryFunc(w)=>f.write_fmt(format_args!("func[{}]",w))
        }?;
        if self.arglist.len()>0 {
            f.write_str("(")?;
            for (i,e) in self.arglist.iter().enumerate() {
                f.write_fmt(format_args!("{:?}",e))?;
                if i!=self.arglist.len()-1 {
                    f.write_str(",")?;
                }
            }
            f.write_str(")")?;
        }
        f.write_fmt(format_args!("->{:?}",self.fin))?;
        Ok(())
    }
}

struct NFTAline<'a,T:Debug> {
    token:Transition,
    arglist:&'a Vec<T>,
    fin:T
}
impl<'a,T:Debug> Debug for NFTAline<'a,T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match self.token {
            // Constant(x)=>f.write_fmt(format_args!("const[{:?}]",x)),
            Input=>f.write_str("input"),
            Destruct(c,i)=>f.write_fmt(format_args!("destruct[{},{}]",c,i)),
            Transition::Construct(c)=>f.write_fmt(format_args!("construct[{}]",c)),
            Switch(_)=>f.write_str("switch"),
            Recursion=>f.write_str("recursion"),
            ArbitraryFunc(w)=>f.write_fmt(format_args!("func[{}]",w))
        }?;
        if self.arglist.len()>0 {
            f.write_str("(")?;
            for (i,e) in self.arglist.iter().enumerate() {
                f.write_fmt(format_args!("{:?}",e))?;
                if i!=self.arglist.len()-1 {
                    f.write_str(",")?;
                }
            }
            f.write_str(")")?;
        }
        f.write_fmt(format_args!("->{:?}",self.fin))?;
        Ok(())
    }
}

pub fn number_to_string(u:usize) -> String {
    u.to_string()
    // let mut string = String::new();
    // loop {
    //     let b = u%26;
    //     string.push(u8::try_from(b+65).unwrap() as char);
    //     u=u/26;
    //     if u==0 {break;}
    // } string
}

pub struct AcceptingStates<'a> {
    pub s:&'a HashSet<usize>
}

impl<'a> Debug for AcceptingStates<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        let mut builder = f.debug_set();
        for s in self.s {
            builder.entry(&number_to_string(*s));
        }
        builder.finish()
    }
}


pub struct DebugPartialNFTA<'a,N> {
    pub t:&'a PartialNFTA<N>,
    pub expr:&'a ExpressionBuilder,
}
impl<'a,N:Debug+Copy> Debug for DebugPartialNFTA<'a,N> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        let mut builder = f.debug_list();
        for (last,ab) in &self.t.rules {
            if ab.len()==0 {panic!("empty entry")}
            for (tok,rest) in ab {
                builder.entry(&DebugNFTAline{expr:self.expr,token:*tok,arglist:rest,fin:*last});
            }
        }
        builder.finish()
    }
}

impl<N:Debug+Copy> Debug for PartialNFTA<N> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        let mut builder = f.debug_list();
        for (last,ab) in &self.rules {
            if ab.len()==0 {panic!("empty entry")}
            for (tok,rest) in ab {
                builder.entry(&NFTAline{token:*tok,arglist:rest,fin:*last});
            }
        }
        builder.finish()
    }
}



pub struct DebugExpressionContext<'a> {
    pub t:Rc<ExpressionContext>,
    pub expr:&'a ExpressionBuilder
}
impl<'a> Debug for DebugExpressionContext<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        let mut builder = f.debug_map();
        builder.entries(
            self.t.exprs.iter().map(|(a,(b,c,_))|(a,(b,DebugType{t:*c,depth:5,expr:self.expr}))),
        );
        builder.finish()
    }
}



pub struct DebugType<'a> {
    pub t:usize,
    pub expr:&'a ExpressionBuilder,
    pub depth:usize
}
impl<'a> Debug for DebugType<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        if self.depth==0 {return f.write_str("...")}
        if let Some(x) = self.expr.debug_type_names.get(&self.t) {return f.write_str(x)}
        match &self.expr.types[self.t] {
            EnumType(a)=>{
                let mut builder = f.debug_tuple("EnumType");
                for j in a {
                    builder.field(&j.iter().map(|k|DebugType{t:*k,expr:self.expr,depth:self.depth-1}).collect::<Vec<_>>());
                }
                builder.finish()
            }
            ProcType::ArrowType(a,b)=>{
                let mut builder = f.debug_tuple("ArrowType");
                builder.field(&DebugType{t:*a,expr:self.expr,depth:self.depth-1});
                builder.field(&DebugType{t:*b,expr:self.expr,depth:self.depth-1});
                builder.finish()
            }
            Placeholder=>f.write_str("Placeholder"),
        }
    }
}



pub struct DebugValue<'a> {
    pub t:usize,
    pub expr:&'a ExpressionBuilder
}
impl<'a> Debug for DebugValue<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match &self.expr.values[self.t].0 {
            Const(a,b)=>{
                let mut builder = f.debug_tuple(&self.expr.constructors[*a].name.clone().unwrap_or(String::from("")));
                for c in b {
                    builder.field(&DebugValue{t:*c,expr:self.expr});
                }
                builder.finish()
            }
            FuncAsValue(a)=>{
                let mut builder = f.debug_tuple("FuncAsValue");
                builder.field(&a);
                builder.finish()
            }
            Uneval=>f.write_str("Uneval"),
        }
    }
}



pub struct EnhancedPrintDsl<'a> {
    pub dsl:&'a Dsl,
    pub expr:&'a ExpressionBuilder
}
impl<'a> Debug for EnhancedPrintDsl<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match self.dsl {
            RecursivePlaceholder => f.write_fmt(format_args!("RecursivePlaceholder")),
            TransferStack(a, b) => {
                let mut builder = f.debug_tuple("TransferStack");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.field(b);
                builder.finish()
            }
            AccessStack(a) => f.write_fmt(format_args!("AccessStack({})",a)),
            ApplyStack(a, b) => {
                let mut builder = f.debug_tuple("ApplyStack");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.field(&b.iter().map(|b|EnhancedPrintDsl{dsl:b,expr:self.expr}).collect::<Vec<_>>());
                builder.finish()
            }
            Dsl::Construct(x,a) => {
                let mut builder = f.debug_tuple(&self.expr.constructors[*x].name.clone().unwrap_or(String::from("")));
                for b in a {
                    builder.field(&EnhancedPrintDsl{dsl:b,expr:self.expr});
                }
                builder.finish()
            }
            BaseValue(a) => DebugValue{t:*a,expr:self.expr}.fmt(f),
            SwitchValue(a, b) => {
                let mut builder = f.debug_tuple("SwitchValue");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                for c in b {
                    builder.field(&EnhancedPrintDsl{dsl:c,expr:self.expr});
                }
                builder.finish()
            }
            Deconstruct(x,y,a) => {
                let mut builder = f.debug_tuple("Deconstruct");
                if let Some(z) = self.expr.constructors[*x].name.clone() {
                    builder.field(&z);
                }
                builder.field(&y);
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.finish()
            }
            EqProg(a, b) => {
                let mut builder = f.debug_tuple("EqProg");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.field(&EnhancedPrintDsl{dsl:b,expr:self.expr});
                builder.finish()
            }
            NeqProg(a, b) => {
                let mut builder = f.debug_tuple("NeqProg");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.field(&EnhancedPrintDsl{dsl:b,expr:self.expr});
                builder.finish()
            }
        }
    }
}


impl Debug for Dsl {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match self {
            RecursivePlaceholder => f.write_fmt(format_args!("RecursivePlaceholder")),
            TransferStack(a, b) => {
                let mut builder = f.debug_tuple("TransferStack");
                builder.field(a);
                builder.field(b);
                builder.finish()
            }
            AccessStack(a) => f.write_fmt(format_args!("AccessStack({})",a)),
            ApplyStack(a, b) => {
                let mut builder = f.debug_tuple("ApplyStack");
                builder.field(a);
                builder.field(b);
                builder.finish()
            }
            Dsl::Construct(x,a) => {
                let mut builder = f.debug_tuple("Construct");
                builder.field(&x);
                for b in a {
                    builder.field(&b);
                }
                builder.finish()
            }
            BaseValue(a) => f.write_fmt(format_args!("BaseValue({})",a)),
            SwitchValue(a, b) => {
                let mut builder = f.debug_tuple("SwitchValue");
                builder.field(a);
                for c in b {
                    builder.field(c);
                }
                builder.finish()
            }
            Deconstruct(x,y,a) => {
                let mut builder = f.debug_tuple("Deconstruct");
                builder.field(&x);
                builder.field(&y);
                builder.field(&a);
                builder.finish()
            }
            EqProg(a, b) => {
                let mut builder = f.debug_tuple("EqProg");
                builder.field(a);
                builder.field(b);
                builder.finish()
            }
            NeqProg(a, b) => {
                let mut builder = f.debug_tuple("NeqProg");
                builder.field(a);
                builder.field(b);
                builder.finish()
            }
        }
    }
}

impl<'a> Debug for Program<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match self {
            AppProg(a) => {
                let mut builder = f.debug_tuple("AppProg");
                for b in a {builder.field(b);}
                builder.finish()
            }
            TupleProg(a) => {
                let mut builder = f.debug_tuple("TupleProg");
                for b in a {builder.field(b);}
                builder.finish()
            }
            FixpointProg(a, b, c) => {
                let mut builder = f.debug_tuple("FixpointProg");
                builder.field(a);
                builder.field(b);
                builder.field(c);
                builder.finish()
            }
            MatchProg(a, b) => {
                let mut builder = f.debug_tuple("MatchProg");
                builder.field(a);
                builder.field(b);
                builder.finish()
            }
            FunProg(a, b, c) => {
                let mut builder = f.debug_tuple("FunProg");
                builder.field(a);
                builder.field(b);
                builder.field(c);
                builder.finish()
            }
            NumericProg(a) => f.write_fmt(format_args!("NumericProg({})",a)),
            IdentProg(a) => a.fmt(f),
            ComparisonProg(a, b) => {
                let mut builder = f.debug_tuple("ComparisonProg");
                builder.field(a);
                builder.field(b);
                builder.finish()
            }
            NegComparisonProg(a, b) => {
                let mut builder = f.debug_tuple("NegComparisonProg");
                builder.field(a);
                builder.field(b);
                builder.finish()
            }
            AccProg(a, b) => {
                let mut builder = f.debug_tuple("AccProg");
                builder.field(a);
                builder.field(b);
                builder.finish()
            }
        }
    }
}

impl<'a> Debug for Value<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match self {
            NumericValue(a) => f.write_fmt(format_args!("NumericValue({})",a)),
            IdentValue(a) => a.fmt(f),
            AppValue(a) => {
                let mut builder = f.debug_tuple("AppValue");
                for b in a {builder.field(b);}
                builder.finish()
            }
            TupleValue(a) => {
                let mut builder = f.debug_tuple("TupleValue");
                for b in a {builder.field(b);}
                builder.finish()
            }
        }
    }
}

impl<'a> Debug for Type<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match self {
            StarType(a) => {
                let mut builder = f.debug_tuple("TupleType");
                for j in a {
                    builder.field(j);
                }
                builder.finish()
            }
            Type::ArrowType(a, b) => {
                let mut builder = f.debug_tuple("ArrowType");
                builder.field(a);
                builder.field(b);
                builder.finish()
            }
            IdentType(a) => a.fmt(f)
        }
    }
}
