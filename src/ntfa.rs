

use std::collections::HashMap;
use std::collections::HashSet;
// use std::collections::hash_map::DefaultHasher;
use std::collections::hash_map::Entry::*;
use std::mem::{take};
use std::iter::{*};
use crate::dsl::{*};
use crate::nftabuilder::{*};
use std::vec::IntoIter;
use Dsl::{*};
use ProcValue::{*};
use std::cmp::Ordering;
use Ordering::{*};
use TermClassification::{*};
// use std::hash::{Hash, Hasher};

#[derive(Copy,Clone,PartialEq,Eq,Hash,Debug)]
pub enum Transition {
    Constant(usize),
    ArbitraryFunc(usize),
    Destruct(usize,usize),
    Construct(usize),
    Switch(usize),
    Recursion,
    Input,
}
impl PartialOrd for Transition {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self,other) {
            (Constant(x),Constant(y)) => Some(x.cmp(y)),
            (Constant(_),_)=>Some(Less),
            (_,Constant(_))=>Some(Greater),
            (ArbitraryFunc(x),ArbitraryFunc(y)) => Some(x.cmp(y)),
            (ArbitraryFunc(_),_)=>Some(Less),
            (_,ArbitraryFunc(_))=>Some(Greater),
            (Destruct(x,a),Destruct(y,b)) => Some((x,a).cmp(&(y,b))),
            (Destruct(_,_),_)=>Some(Less),
            (_,Destruct(_,_))=>Some(Greater),
            (Transition::Construct(x),Transition::Construct(y)) => Some(x.cmp(y)),
            (Transition::Construct(_),_)=>Some(Less),
            (_,Transition::Construct(_))=>Some(Greater),
            (Switch(x),Switch(y)) => Some(x.cmp(y)),
            (Switch(_),_)=>Some(Less),
            (_,Switch(_))=>Some(Greater),
            (Recursion,Recursion) => Some(Equal),
            (Recursion,_) => Some(Less),
            (_,Recursion) => Some(Greater),
            (Input,Input) => Some(Equal)
        }
    }
}
impl Ord for Transition {
    fn cmp(&self,other:&Self) -> Ordering {
        match (self,other) {
            (Constant(x),Constant(y)) => x.cmp(y),
            (Constant(_),_)=>Less,
            (_,Constant(_))=>Greater,
            (ArbitraryFunc(x),ArbitraryFunc(y)) => x.cmp(y),
            (ArbitraryFunc(_),_)=>Less,
            (_,ArbitraryFunc(_))=>Greater,
            (Destruct(x,a),Destruct(y,b)) => (x,a).cmp(&(y,b)),
            (Destruct(_,_),_)=>Less,
            (_,Destruct(_,_))=>Greater,
            (Transition::Construct(x),Transition::Construct(y)) => x.cmp(y),
            (Transition::Construct(_),_)=>Less,
            (_,Transition::Construct(_))=>Greater,
            (Switch(x),Switch(y)) => x.cmp(y),
            (Switch(_),_)=>Less,
            (_,Switch(_))=>Greater,
            (Recursion,Recursion) => Equal,
            (Recursion,_) => Less,
            (_,Recursion) => Greater,
            (Input,Input) => Equal
        }
    }
}

use Transition::{*};
pub struct NTFABuilder {
    pub input_type:usize,
    pub output_type:usize,
    pub paths:Vec<(Vec<(Transition,Vec<usize>)>,Option<usize>,Vec<(usize,(usize,TermClassification))>)>,//inner vec must be sorted
    // pub revhash:HashMap<u64,Vec<usize>>,
    pub intersect_memo:HashMap<(usize,usize),Option<usize>>,//left side of key is less than right side
    // pub rename_memo:HashMap<(usize,Vec<usize>),usize>,
    // pub subset_memo:HashMap<(usize,usize),bool>,
    // minification_queue:Vec<usize>,
    pub purgeset:HashSet<usize>
}

impl NTFABuilder {
    pub fn purge(&mut self,h:usize) {
        let mut stack : Vec<usize> = vec![h];
        while let Some(z) = stack.pop() {
            if z==0 {continue;}
            if self.paths[z].0.len()==0 {panic!("purge failed! {:?}",z);}
            if let None = self.paths[z].1 {panic!("purge failed (accessibility cleaning)!");}
            for (_,a) in self.paths[z].0.iter() {
                for c in a.iter().copied() {
                    if self.purgeset.insert(c) {
                        stack.push(c);
                    }
                }
            }
        }
    }
    pub fn get_ntfa(&mut self,mut deps:Vec<(Transition,Vec<usize>)>,interp:Vec<(usize,(usize,TermClassification))>)->usize {
        if deps.len()==0 {panic!()}
        deps.sort_unstable();
        deps.dedup();
        // match self.revhash.entry(deps) {
        //     Occupied(x)=>*x.get(),
        //     Vacant(x)=>{
        //         let i=self.paths.len();
        //         // if NTFABuilder::check_requires_further(x.key()) {
        //         //     self.minification_queue.push(i);
        //         // }
        //         self.paths.push(x.key().clone());
        //         x.insert(i); i
        //     }
        // }
        let k = deps.iter().filter_map(|(_,r)| if let Some(p) = r.iter().map(|z|self.paths[*z].1).reduce(|x,y|match (x,y) {
            (Some(x),Some(y)) => Some(x+y),
            _ => None
        }) {p.map(|p|p+1)} else {Some(1)}).min();
        let i=self.paths.len();
        self.paths.push((deps,k,interp)); i
    }

    pub fn get_placeholder(&mut self)->usize {
        self.paths.push((Vec::new(),None,Vec::new()));
        self.paths.len()-1
    }

    pub fn insert_into_placeholder(&mut self,mut deps:Vec<(Transition,Vec<usize>)>,i:usize,interp:Vec<(usize,(usize,TermClassification))>)->usize {
        if deps.len()==0 {panic!()}
        deps.sort_unstable();
        deps.dedup();
        // let mut s = DefaultHasher::new();
        // deps.hash(&mut s);
        let k = deps.iter().filter_map(|(_,r)| if let Some(p) = r.iter().map(|z|self.paths[*z].1).reduce(|x,y|match (x,y) {
            (Some(x),Some(y)) => Some(x+y),
            _ => None
        }) {p.map(|p|p+1)} else {Some(1)}).min();
        // let gh = self.revhash.entry(s.finish()).or_default();
        // for g in gh.iter() {
        //     if self.paths[*g].0==deps {
        //         self.paths[i]=(deps,k,interp);
        //         return *g;
        //     }
        // }
        self.paths[i]=(deps,k,interp);
        // gh.push(i); 
        i
    }
}




// pub type NTFA = usize;
// #[derive(Default)]
// pub struct ValueMapper {
//     // pub recursion:HashMap<usize,HashSet<usize>>,
//     // truthiness:HashMap<usize,bool>,
//     pub statemap:HashMap<usize,Vec<(usize,usize)>>
// }


// //dimensions: {interpretation:[options]}


// impl ValueMapper {
//     fn new()->Self {
//         ValueMapper {
//             statemap:HashMap::new(),
//             // recursion:HashMap::new(),
//             // // truthiness:HashMap::new(),
//             // remap:HashMap::new()
//         }
//     }
//     fn union(&mut self,a:usize,b:Vec<usize>) {
//         let r : Vec<_> = b.iter().map(|z|self.statemap[z]).flatten().collect();
//         self.statemap.insert(a,r);
//     }
// }


        // 0:unit        (0)
        // 1:input       (0)

        // 2:pair        (2)

        // 3:fst         (1)
        // 4:snd         (1)
        // 7:unl         (1)
        // 8:unr         (1)

        // 9:switch      (3)

        // 5:inl         (1)
        // 6:inr         (1)

        // 10:recursion  (1)
        // 11-onwards: free space!

impl NTFABuilder {

    // Constant(usize),
    // ArbitraryFunc(usize),
    // Destruct(usize,usize),
    // Construct(usize),
    // Switch,
    // Recursion,
    // Input,

    
    // AccessStack(usize),
    // ApplyStack(Box<Dsl>,Vec<Dsl>),
    // Deconstruct(usize,usize),
    // Construct(usize,Vec<Dsl>),
    // BaseValue(usize),
    // SwitchValue(Box<Dsl>,Vec<Dsl>),

    pub fn debug_is_accepting_run(&self,ntfa:usize,d:&Dsl,ex:&ExpressionBuilder)->bool {
        if ntfa==0 {return true;}
        let (dslf,dsla) = match d {
            AccessStack(0)=>(Input,Vec::new()),
            BaseValue(x)=>(Constant(*x),Vec::new()),
            SwitchValue(c,b)=>(Switch(b.len()),once(*c.clone()).chain(b.iter().cloned()).collect()),
            Deconstruct(x,y,a)=>(Destruct(*x,*y),vec![*a.clone()]),
            Dsl::Construct(x,a)=>(Transition::Construct(*x),a.clone()),
            ApplyStack(j,b) => match &**j {
                RecursivePlaceholder => (Recursion,b.clone()),
                BaseValue(x) => match ex.values[*x].0 {
                    FuncAsValue(f) => (ArbitraryFunc(f),b.clone()),
                    _ => panic!()
                },
                _ => panic!()
            },
            _=>panic!()
        };
        for (f,a) in self.paths[ntfa].0.iter() {
            if *f==dslf {
                if dsla.iter().zip(a.iter()).all(|(da,fa)|
                    self.debug_is_accepting_run(*fa,da,ex)
                ) {return true;}
            }
        } false
    }

    pub fn accessibility_cleaning(&mut self,extrapass:&[usize],k_limit:Option<usize>) {
        loop {
            let mut hot = false;
            for u in extrapass {
                let mut k = self.paths[*u].0.iter().filter_map(|(_,r)| if let Some(p) = r.iter().map(|z|self.paths[*z].1).reduce(|x,y|match (x,y) {
                    (Some(x),Some(y)) => Some(x+y),
                    _ => None
                }) {p.map(|p|p+1)} else {Some(1)}).min();
                if let (Some(z),Some(z_lim)) = (k,k_limit) {
                    if z>z_lim {k=None}
                }
                if self.paths[*u].1!=k {
                    self.paths[*u].1=k;
                    hot = true;
                }
            }
            if !hot {break;}
        }
        for u in extrapass {
            if self.paths[*u].1.is_none() {continue;}
            let buffer = self.paths[*u].0.iter().map(|(_,r)|r.iter().all(|i|self.paths[*i].1.is_some())).collect::<Vec<_>>();
            let mut index = 0;
            self.paths[*u].0.retain(|_|{index+=1;buffer[index-1]});
        }
    }
}

#[derive(Clone,Copy,PartialEq,PartialOrd,Eq,Ord,Hash,Debug)]
pub enum TermClassification {
    Introduction,
    Elimination
}
#[derive(Default)]
pub struct PartialNTFA {
    pub rules:HashMap<(usize,TermClassification),Vec<(Transition,Vec<(usize,TermClassification)>)>>,
    // occurances:HashMap<usize,HashSet<usize>>,
    // maxins:usize,
    // vm:ValueMapper
}
impl PartialNTFA {
    pub fn new()->Self {PartialNTFA{rules:HashMap::new()}}
    pub fn add_rule(&mut self,f:Transition,a:Vec<(usize,TermClassification)>,r:(usize,TermClassification)) {
        // let mut m=r;
        // for a in a.iter() {
        //     if *a>m {m=*a;}
        //     self.occurances.entry(*a).or_default().insert(r);
        // }
        // if m>=self.maxins {self.maxins=m+1;}
        self.rules.entry(r).or_default().push((f,a));
    }
    pub fn convert(self,builder:&mut NTFABuilder,accstates:&Vec<(usize,TermClassification)>,interp:usize)->Vec<usize> {
        #[derive(Debug)]
        struct ArtificialStack {
            outercollect: Vec<(Transition,Vec<usize>)>,
            innercollect: Vec<usize>,
            outertrav: IntoIter<(Transition,Vec<(usize,TermClassification)>)>,
            innertrav: Vec<(usize,TermClassification)>,
            innertoken: Transition,
            // target: usize,
            place: usize,
            // types: InvType
        }
        let mut extrapass = Vec::new();
        let mut memo:HashMap<(usize,TermClassification),Option<usize>> = HashMap::new();
        memo.insert((0,Introduction),Some(0));
        let mut result = Vec::new();
        for accstate in accstates.iter().copied() {
            // println!("STATE BOUNDARY -=-=-=-=--=-=-=-=-=-=-=-=-=-=-=");
            let mut stack:Vec<ArtificialStack> = Vec::new();
            let place = match memo.entry(accstate) {
                Occupied(z)=>{
                    if let Some(w) = *z.get() {
                        result.push(w);
                    }
                    continue;
                }
                Vacant(z)=>{
                    let place = builder.get_placeholder();
                    z.insert(Some(place));place
                }
            };
            // let intype = BaseType(builder.output_type);
            let mut outertrav = match self.rules.get(&accstate) {None=>{continue;} Some(y)=>y}.clone();
            outertrav.sort_unstable();outertrav.dedup();
            for (_,j) in outertrav.iter_mut() {j.reverse()}
            let mut outertrav = outertrav.into_iter();
            let (innertoken,intv) = outertrav.next().unwrap();
            stack.push(ArtificialStack{
                outercollect:Vec::new(),
                innercollect:Vec::new(),
                outertrav,
                innertoken,
                innertrav:intv,
                place,
                // target: accstate
                // types: intype
            });
            // println!("MEMO: {:?}",memo);

            while stack.len()>0 {
                let x = stack.last_mut().unwrap();
                loop {
                    if let Some(subl) = x.innertrav.pop() {
                        match memo.get(&subl).copied() {
                            Some(Some(y))=>{
                                // println!("using memo element: {:?}",y);
                                x.innercollect.push(y);
                                continue;
                            }
                            Some(None)=>{x.innercollect.clear();}
                            None=>{
                                let mut outertrav = self.rules[&subl].clone();
                                outertrav.sort_unstable();outertrav.dedup();
                                for (_,j) in outertrav.iter_mut() {j.reverse()}
                                let mut outertrav = outertrav.into_iter();
                                if let Some((innertoken,intv)) = outertrav.next() {
                                    let place = builder.get_placeholder();
                                    extrapass.push(place);
                                    // assoc.insert(place,vec![subl]);
                                    memo.insert(subl,Some(place));
                                    x.innertrav.push(subl);
                                    // println!("pushing: {:?}, placeholder = {:?}",subl,place);
                                    // let nn = x.types.over(x.innertoken,x.innercollect.len(),builder,ex);
                                    stack.push(ArtificialStack{
                                        outercollect:Vec::new(),
                                        innercollect:Vec::new(),
                                        outertrav,
                                        innertoken,
                                        innertrav:intv,
                                        // target: subl,
                                        place,
                                        // types:nn
                                    });
                                    break;
                                } else {x.innercollect.clear();}
                            }
                        }
                    } else {
                        let v = take(&mut x.innercollect);
                        x.outercollect.push((x.innertoken,v));
                    }
                    if let Some((innertoken,intv))=x.outertrav.next() {
                        x.innertoken=innertoken;
                        x.innertrav=intv;
                    } else {
                        let ff = stack.pop().unwrap();
                        let lastval = match stack.last() {
                            Some(x)=>*x.innertrav.last().unwrap(),
                            None=>accstate
                        };
                        let rpv = if ff.outercollect.len()==0 {None} else {
                            let u = builder.insert_into_placeholder(ff.outercollect,ff.place,vec![(interp,lastval)]);
                            extrapass.push(u);
                            Some(u)
                        };
                        if rpv != Some(ff.place) {
                            memo.insert(lastval,rpv);//harmlessly replace old value
                        }
                        if stack.len()==0 {
                            if let Some(z)=rpv {
                                result.push(z);
                            }
                        }
                        break;
                    }
                }
            }
        }
        builder.accessibility_cleaning(&extrapass,None);
        result.retain(|h|builder.paths[*h].1.is_some());
        result
    }
}



