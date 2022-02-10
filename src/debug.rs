
use crate::dsl::{Dsl,ExpressionContext};
use crate::mlsparser::{Program,Value,Type};
use crate::nftabuilder::{ExpressionBuilder,ProcType,ProcValue,Constname};
// use crate::ntfa::{PartialNTFA,NTFABuilder};
// use std::fmt::Write;
use core::fmt::{Debug,Formatter,Error};
// use std::collections::HashMap;
// use std::collections::VecDeque;
// use std::collections::hash_map::Entry::*;
use std::collections::HashSet;
use std::rc::Rc;
use Dsl::{*};
use Program::{*};
use Value::{*};
use Type::{*};
use ProcType::{*};
use ProcValue::{*};
use Constname::{*};



pub fn debug_expectedlen(token:usize)->Option<usize> {
    match token {
        0=>Some(0),1=>Some(0),
        2=>Some(2),
        3=>Some(1),4=>Some(1),
        5=>Some(1),6=>Some(1),
        7=>Some(1),8=>Some(1),
        9=>Some(3),
        10=>Some(1),
        _=>None
    }
}
// impl NTFABuilder {
//     pub fn count_relevant_states(&self,a:usize) {
//         let mut relevant = HashSet::new();
//         let mut stack = vec![a];
//         while let Some(a) = stack.pop() {
//             if !relevant.insert(a) {continue;}
//             for (_,row) in self.paths[a].iter() {
//                 stack.extend(row.iter().copied());
//             }
//         }
//         println!("relevant states: {}",relevant.len());
//     }
//     pub fn output_tree(&self,a:usize)->Result<(),Error> {
//         let mut relevant = HashMap::new();
//         relevant.insert(a,0);
//         let mut index = 1;
//         let mut queue = VecDeque::new();
//         queue.push_back((a,0));
//         let mut buffer = String::new();
//         while let Some((a,iu)) = queue.pop_front() {
//             if iu != 0 {buffer.write_char(',')?;}
//             for (iu,(f,row)) in self.paths[a].iter().enumerate() {
//                 if iu != 0 {buffer.write_char('|')?;}
//                 match f {
//                     0=>buffer.write_str("unit"),1=>buffer.write_str("input"),
//                     2=>buffer.write_str("pair"),
//                     3=>buffer.write_str("fst"),4=>buffer.write_str("snd"),
//                     5=>buffer.write_str("inl"),6=>buffer.write_str("inr"),
//                     7=>buffer.write_str("unl"),8=>buffer.write_str("unr"),
//                     9=>buffer.write_str("switch"),
//                     10=>buffer.write_str("recursion"),
//                     w=>buffer.write_fmt(format_args!("func{}",w))
//                 }?;
//                 buffer.write_char('(')?;
//                 for (iu,r) in row.iter().enumerate() {
//                     if iu != 0 {buffer.write_char(',')?;}
//                     let ii = match relevant.entry(*r) {
//                         Occupied(x)=>{*x.get()}
//                         Vacant(x)=>{x.insert(index);queue.push_back((*r,index));index+=1;index-1}
//                     };
//                     buffer.write_fmt(format_args!("{}",ii))?;
//                 }
//                 buffer.write_char(')')?;
//             }
//         }
//         println!("FTA: {}",buffer);
//         Ok(())
//     }
// }

struct NTFAline {
    token:usize,
    arglist:Vec<String>,
    fin:String,
}
impl<'a> Debug for NTFAline {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match self.token {
            0=>f.write_str("()"),1=>f.write_str("input"),
            2=>f.write_str("pair"),
            3=>f.write_str("fst"),4=>f.write_str("snd"),
            5=>f.write_str("inl"),6=>f.write_str("inr"),
            7=>f.write_str("unl"),8=>f.write_str("unr"),
            9=>f.write_str("switch"),
            10=>f.write_str("recursion"),
            w=>f.write_fmt(format_args!("func({})",w))
        }?;
        if self.arglist.len()>0 {
            f.write_str("(")?;
            for (i,e) in self.arglist.iter().enumerate() {
                f.write_fmt(format_args!("{}",e))?;
                if i!=self.arglist.len()-1 {
                    f.write_str(",")?;
                }
            }
            f.write_str(")")?;
        }
        f.write_fmt(format_args!("->{}",self.fin))?;
        Ok(())
    }
}

pub fn number_to_string(mut u:usize) -> String {
    let mut string = String::new();
    loop {
        let b = u%26;
        string.push(u8::try_from(b+65).unwrap() as char);
        u=u/26;
        if u==0 {break;}
    } string
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


// impl Debug for PartialNTFA {
//     fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
//         let mut builder = f.debug_list();
//         for (last,ab) in &self.rules {
//             if ab.len()==0 {panic!("empty entry")}
//             for (tok,rest) in ab {
//                 builder.entry(&NTFAline{token:*tok,arglist:rest.iter().copied().map(number_to_string).collect(),fin:number_to_string(*last)});
//             }
//         }
//         builder.finish()
//     }
// }



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
        match self.expr.types[self.t] {
            PairType(a,b)=>{
                let mut builder = f.debug_tuple("PairType");
                builder.field(&DebugType{t:a,expr:self.expr,depth:self.depth-1});
                builder.field(&DebugType{t:b,expr:self.expr,depth:self.depth-1});
                builder.finish()
            }
            ProcType::ArrowType(a,b)=>{
                let mut builder = f.debug_tuple("ArrowType");
                builder.field(&DebugType{t:a,expr:self.expr,depth:self.depth-1});
                builder.field(&DebugType{t:b,expr:self.expr,depth:self.depth-1});
                builder.finish()
            }
            LRType(a,b)=>{
                let mut builder = f.debug_tuple("LRType");
                builder.field(&DebugType{t:a,expr:self.expr,depth:self.depth-1});
                builder.field(&DebugType{t:b,expr:self.expr,depth:self.depth-1});
                builder.finish()
            }
            UnitType=>f.write_str("Unit"),
            Placeholder=>f.write_str("Placeholder"),
        }
    }
}



pub struct DebugTypedValue<'a> {
    pub val:usize,
    pub ty:usize,
    pub expr:&'a ExpressionBuilder
}
impl<'a> Debug for DebugTypedValue<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match (&self.expr.values[self.val].0,&self.expr.types[self.ty]) {
            (PairValue(a,b),PairType(at,bt))=>{
                let mut builder = f.debug_tuple("");
                builder.field(&DebugTypedValue{val:*a,ty:*at,expr:self.expr});
                let mut val=*b;
                let mut ty=*bt;
                loop {
                    match (&self.expr.values[val].0,&self.expr.types[ty]) {
                        (PairValue(a,b),PairType(at,bt))=>{
                            builder.field(&DebugTypedValue{val:*a,ty:*at,expr:self.expr});
                            val=*b;ty=*bt;
                        }
                        _=>{
                            builder.field(&DebugTypedValue{val:val,ty:ty,expr:self.expr});
                            break;
                        }
                    }
                }
                builder.finish()
            }
            (LValue(_)|RValue(_),_)=>{
                match self.expr.debug_constr_names.get(&self.ty) {
                    None=>match (&self.expr.values[self.val].0,&self.expr.types[self.ty]) {
                        (LValue(a),LRType(at,_))=>{
                            let mut builder = f.debug_tuple("LValue");
                            builder.field(&DebugTypedValue{val:*a,ty:*at,expr:self.expr});
                            builder.finish()
                        }
                        (RValue(a),LRType(_,at))=>{
                            let mut builder = f.debug_tuple("RValue");
                            builder.field(&DebugTypedValue{val:*a,ty:*at,expr:self.expr});
                            builder.finish()
                        }
                        _=>panic!()
                    }
                    Some(mut x)=>{
                        let mut val=self.val;
                        let mut ty=self.ty;
                        loop {
                            match x {
                                NullaryName(x)=>{break f.write_str(x)}
                                UnaryName(x)=>{
                                    let mut builder = f.debug_tuple(x);
                                    loop {
                                        match (&self.expr.values[val].0,&self.expr.types[ty]) {
                                            (PairValue(a,b),PairType(at,bt))=>{
                                                builder.field(&DebugTypedValue{val:*a,ty:*at,expr:self.expr});
                                                val=*b;ty=*bt;
                                            }
                                            _=>{
                                                builder.field(&DebugTypedValue{val:val,ty:ty,expr:self.expr});
                                                break;
                                            }
                                        }
                                    }
                                    break builder.finish()
                                }
                                LRSplit(b,c)=>match (&self.expr.values[val].0,&self.expr.types[ty]) {
                                    (LValue(a),LRType(at,_))=>{val=*a;ty=*at;x=b;}
                                    (RValue(a),LRType(_,at))=>{val=*a;ty=*at;x=c;}
                                    _=>panic!()
                                }
                            }
                        }
                    }
                }
            }
            (FuncAsValue(a),_)=>{
                let mut builder = f.debug_tuple("FuncAsValue");
                builder.field(&a);
                builder.finish()
            }
            (UnitValue,UnitType)=>f.write_str("Unit"),
            (Uneval,_)=>f.write_str("Uneval"),
            _=>{
                let mut builder = f.debug_tuple("Value_Type_Mismatch");
                builder.field(&DebugValue{t:self.val,expr:self.expr});
                builder.field(&DebugType{t:self.ty,depth:5,expr:self.expr});
                builder.finish()
            }
        }
    }
}






pub struct DebugValue<'a> {
    pub t:usize,
    pub expr:&'a ExpressionBuilder
}
impl<'a> Debug for DebugValue<'a> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match self.expr.values[self.t].0 {
            PairValue(a,b)=>{
                let mut builder = f.debug_tuple("PairValue");
                builder.field(&DebugValue{t:a,expr:self.expr});
                builder.field(&DebugValue{t:b,expr:self.expr});
                builder.finish()
            }
            LValue(a)=>{
                let mut builder = f.debug_tuple("LValue");
                builder.field(&DebugValue{t:a,expr:self.expr});
                builder.finish()
            }
            RValue(a)=>{
                let mut builder = f.debug_tuple("RValue");
                builder.field(&DebugValue{t:a,expr:self.expr});
                builder.finish()
            }
            FuncAsValue(a)=>{
                let mut builder = f.debug_tuple("FuncAsValue");
                builder.field(&a);
                builder.finish()
            }
            UnitValue=>f.write_str("Unit"),
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
            Lside(a) => {
                let mut builder = f.debug_tuple("Lside");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.finish()
            }
            Rside(a) => {
                let mut builder = f.debug_tuple("Rside");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.finish()
            }
            Pair(a, b) => {
                let mut builder = f.debug_tuple("Pair");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.field(&EnhancedPrintDsl{dsl:b,expr:self.expr});
                builder.finish()
            }
            BaseValue(a) => DebugValue{t:*a,expr:self.expr}.fmt(f),
            SwitchValue(a, b, c) => {
                let mut builder = f.debug_tuple("SwitchValue");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.field(&EnhancedPrintDsl{dsl:b,expr:self.expr});
                builder.field(&EnhancedPrintDsl{dsl:c,expr:self.expr});
                builder.finish()
            }
            LUndo(a) => {
                let mut builder = f.debug_tuple("LUndo");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.finish()
            }
            RUndo(a) => {
                let mut builder = f.debug_tuple("RUndo");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.finish()
            }
            LeftValue(a) => {
                let mut builder = f.debug_tuple("LeftValue");
                builder.field(&EnhancedPrintDsl{dsl:a,expr:self.expr});
                builder.finish()
            }
            RightValue(a) => {
                let mut builder = f.debug_tuple("RightValue");
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
            Lside(a) => {
                let mut builder = f.debug_tuple("Lside");
                builder.field(a);
                builder.finish()
            }
            Rside(a) => {
                let mut builder = f.debug_tuple("Rside");
                builder.field(a);
                builder.finish()
            }
            Pair(a, b) => {
                let mut builder = f.debug_tuple("Pair");
                builder.field(a);
                builder.field(b);
                builder.finish()
            }
            BaseValue(a) => f.write_fmt(format_args!("BaseValue({})",a)),
            SwitchValue(a, b, c) => {
                let mut builder = f.debug_tuple("SwitchValue");
                builder.field(a);
                builder.field(b);
                builder.field(c);
                builder.finish()
            }
            LUndo(a) => {
                let mut builder = f.debug_tuple("LUndo");
                builder.field(a);
                builder.finish()
            }
            RUndo(a) => {
                let mut builder = f.debug_tuple("RUndo");
                builder.field(a);
                builder.finish()
            }
            LeftValue(a) => {
                let mut builder = f.debug_tuple("LeftValue");
                builder.field(a);
                builder.finish()
            }
            RightValue(a) => {
                let mut builder = f.debug_tuple("RightValue");
                builder.field(a);
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
            StarType(a, b) => {
                let mut builder = f.debug_tuple("StarType");
                builder.field(a);
                builder.field(b);
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
