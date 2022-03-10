


use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::BinaryHeap;
use std::collections::hash_map::Entry::*;
use std::rc::Rc;
use std::iter::{*};
use crate::ntfa::{*};
use crate::dsl::{*};
use crate::nftabuilder::{*};
use std::cmp::Ordering;
use Ordering::{*};
use Dsl::{*};
use Transition::{*};


fn disjoint_union(mut a:HashMap<usize,usize>,b:HashMap<usize,usize>) -> Option<HashMap<usize,usize>> {
    for (k,v) in b.into_iter() {
        match a.entry(k) {
            Vacant(hole) => {hole.insert(v);}
            Occupied(spot) => {
                if *spot.get() != v {return None;}
            }
        }
    } Some(a)
}


impl NTFABuilder {

    pub fn get_boring_accepting_run(
        &self,
        start:usize,
        builder:&mut ExpressionBuilder
    ) -> (Dsl,usize,Vec<(usize,usize)>) {
        let mut queue : BinaryHeap<SolutionStatusWrap<InconsistentMapping>> = BinaryHeap::new();
        queue.push(SolutionStatusWrap(start,0,None));
        let mut solns : HashMap<usize,Rc<SolutionStatus<InconsistentMapping>>> = HashMap::new();
        let mut working : HashMap<usize,Vec<(&[usize],Vec<Rc<SolutionStatus<InconsistentMapping>>>,Transition,usize,usize)>> = HashMap::new();
        let mut visited : HashSet<usize> = HashSet::new();
        while let Some(SolutionStatusWrap(x,minsize,updown)) = queue.pop() {
            let mut stack:Vec<(&[usize],Vec<Rc<SolutionStatus<InconsistentMapping>>>,Transition,usize,usize)> = Vec::new();
            match updown {
                None=>{
                    if !visited.insert(x) {continue;}
                    let y = &self.paths[x].0;
                    if let Some((f,_)) = y.iter().find(|(_,x)|x.len()==0) {
                        for sol in SolutionStatus::transfix(*f,&vec![],builder,self,x) {
                            queue.push(SolutionStatusWrap(x,minsize+sol.size,Some(sol)));
                        }
                    } else {
                        for (f,l) in y.iter() {
                            if l.contains(&x) {continue;}
                            stack.push((l,Vec::new(),*f,x,minsize));
                        }
                    }
                }
                Some(sol)=>{
                    let sol = match solns.entry(x) {
                        Occupied(_)=>{continue;}
                        Vacant(y)=>{y.insert(Rc::new(sol))}
                    };
                    for (l,mut v,f,y,minsize) in working.remove(&x).into_iter().flatten() {
                        v.push(sol.clone());
                        stack.push((l,v,f,y,minsize+sol.size));
                    }
                }
            }
            while let Some((l,mut v,f,x,minsize)) = stack.pop() {
                if l.len()==0 {
                    for sol in SolutionStatus::transfix(f,&v,builder,self,x) {
                        queue.push(SolutionStatusWrap(x,minsize,Some(sol)));
                    }
                    continue;
                }
                match solns.get(&l[0]) {
                    None=>{
                        queue.push(SolutionStatusWrap(l[0],minsize,None));
                        working.entry(l[0]).or_default().push((&l[1..],v,f,x,minsize));
                    }
                    Some(sol)=>{
                        v.push(sol.clone());
                        stack.push((&l[1..],v,f,x,minsize+sol.size));
                    }
                }
            }
        }
        let SolutionStatus {dsl:a,size:b,mapping:c,..} = &*solns.remove(&start).unwrap();
        (a.clone(),*b,c.to_vec())
    }



    pub fn get_accepting_runs(
        &self,
        start:usize,
        builder:&mut ExpressionBuilder
    ) -> Vec<(Dsl,usize,Vec<(usize,usize)>)> {
        let mut queue : BinaryHeap<SolutionStatusWrap<ConsistentMapping>> = BinaryHeap::new();
        queue.push(SolutionStatusWrap(start,0,None));
        let mut solns : HashMap<usize,Vec<Rc<SolutionStatus<ConsistentMapping>>>> = HashMap::new();
        let mut working : HashMap<usize,Vec<(&[usize],Vec<Rc<SolutionStatus<ConsistentMapping>>>,Transition,usize,usize)>> = HashMap::new();
        let mut visited : HashSet<usize> = HashSet::new();
        while let Some(SolutionStatusWrap(x,minsize,updown)) = queue.pop() {
            let mut stack:Vec<(&[usize],Vec<Rc<SolutionStatus<ConsistentMapping>>>,Transition,usize,usize)> = Vec::new();
            match updown {
                None=>{
                    if !visited.insert(x) {continue;}
                    let y = &self.paths[x].0;
                    if let Some((f,_)) = y.iter().find(|(_,x)|x.len()==0) {
                        // println!("found nullary!");
                        for sol in SolutionStatus::transfix(*f,&vec![],builder,self,x) {
                            queue.push(SolutionStatusWrap(x,minsize+sol.size,Some(sol)));
                        }
                    } else {
                        for (f,l) in y.iter() {
                            if l.contains(&x) {continue;}
                            stack.push((l,Vec::new(),*f,x,1+minsize));
                        }
                    }
                }
                Some(sol)=>{
                    let sol = match sol.insert(solns.entry(x).or_default()) {None=>{continue;},Some(x)=>x};
                    for (l,v,f,y,minsize) in working.get(&x).into_iter().flatten() {
                        let mut v2=v.clone();
                        v2.push(sol.clone());
                        stack.push((l,v2,*f,*y,minsize+sol.size));
                    }
                }
            }
            while let Some((l,v,f,x,minsize)) = stack.pop() {
                if l.len()==0 {
                    for sol in SolutionStatus::transfix(f,&v,builder,self,x) {
                        queue.push(SolutionStatusWrap(x,minsize,Some(sol)));
                    }
                    continue;
                }
                queue.push(SolutionStatusWrap(l[0],minsize,None));
                for sol in solns.get(&l[0]).into_iter().flatten().cloned() {
                    let mut v2=v.clone();
                    let msz = minsize+sol.size;
                    v2.push(sol);
                    stack.push((&l[1..],v2,f,x,msz));
                }
                working.entry(l[0]).or_default().push((&l[1..],v,f,x,minsize));
            }
        }
        solns.remove(&start).unwrap_or_default().into_iter().map(|x|{
            let SolutionStatus{dsl:a,size:b,mapping:c,..} = &*x;
            (a.clone(),*b,c.to_vec())
        }).collect()
    }
}



trait Mapping : Sized {
    fn empty()->Self;
    fn from_vec(iter:Vec<(usize,usize)>)->Option<Self>;
    fn to_vec(&self)->Vec<(usize,usize)>;
    fn intersect(&self,other:&Self) -> Option<Self>;
    fn subset(&self,other:&Self) -> bool;
}
struct ConsistentMapping(Option<Rc<HashMap<usize,usize>>>);
impl Mapping for ConsistentMapping {
    fn empty() -> Self {ConsistentMapping(None)}
    fn from_vec(iter:Vec<(usize,usize)>) -> Option<Self> {
        let mut hs = HashMap::new();
        for (a,b) in iter {
            match hs.entry(a) {
                Vacant(x)=>{x.insert(b);}
                Occupied(x)=>{if *x.get()!=b {return None;}}
            }
        }
        if hs.len()==0 {return Some(ConsistentMapping(None))}
        Some(ConsistentMapping(Some(Rc::new(hs))))
    }
    fn to_vec(&self)->Vec<(usize,usize)> {
        match &self.0 {
            None=>Vec::new(),
            Some(a)=>a.iter().map(|(k,v)|(*k,*v)).collect()
        }
    }
    fn intersect(&self,other:&Self) -> Option<Self> {
        match (&self.0,&other.0) {
            (None,None)=>Some(ConsistentMapping(None)),
            (Some(x),None)|(None,Some(x))=>Some(ConsistentMapping(Some(x.clone()))),
            (Some(x),Some(y))=>disjoint_union(
                (**x).clone(),
                (**y).clone()
            ).map(|x|ConsistentMapping(Some(Rc::new(x))))
        }
    }
    fn subset(&self,other:&Self) -> bool {
        if let Some(z)=&self.0 {//inserting subset of present
            if let Some(xx)=&other.0 {z.iter().all(|(k,v)|xx.get(k)==Some(v))}
            else {false}
        } else {true}
    }
}
struct InconsistentMapping(Option<Rc<Vec<(usize,usize)>>>);
impl Mapping for InconsistentMapping {
    fn empty() -> Self {InconsistentMapping(None)}
    fn from_vec(iter:Vec<(usize,usize)>) -> Option<Self> {
        if iter.len()==0 {return Some(InconsistentMapping(None))}
        Some(InconsistentMapping(Some(Rc::new(iter))))
    }
    fn to_vec(&self)->Vec<(usize,usize)> {
        match &self.0 {
            None=>Vec::new(),
            Some(a)=>a.iter().copied().collect()
        }
    }
    fn intersect(&self,other:&Self) -> Option<Self> {
        match (&self.0,&other.0) {
            (None,None)=>Some(InconsistentMapping(None)),
            (Some(x),None)|(None,Some(x))=>Some(InconsistentMapping(Some(x.clone()))),
            (Some(x),Some(y))=>Some(InconsistentMapping(Some(Rc::new(x.iter().cloned().chain(y.iter().cloned()).collect()))))
        }
    }
    fn subset(&self,_:&Self) -> bool {true}
}


#[derive(Clone,Debug)]
struct SolutionStatus<M:Mapping> {
    dsl:Dsl,
    size:usize,
    mapping:M,
    node:usize
}
#[derive(Debug)]
struct SolutionStatusWrap<M:Mapping>(usize,usize,Option<SolutionStatus<M>>);
impl<M:Mapping> Eq for SolutionStatusWrap<M> {}
impl<M:Mapping> Ord for SolutionStatusWrap<M> {
    fn cmp(&self, other: &Self) -> Ordering {other.1.cmp(&self.1)}
}
impl<M:Mapping> PartialOrd for SolutionStatusWrap<M> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {Some(other.1.cmp(&self.1))}
}
impl<M:Mapping> PartialEq<SolutionStatusWrap<M>> for SolutionStatusWrap<M> {
    fn eq(&self, other: &Self) -> bool {self.1 == other.1}
}

impl<M:Mapping> SolutionStatus<M> {
    fn compare_usefulness(&self,other:&SolutionStatus<M>)->Ordering {
        let SolutionStatus{size:s,mapping:m,..} = other;
        match (m.subset(&self.mapping),self.mapping.subset(m),self.size.cmp(s)) {
            (true,_,Greater|Equal)=>Less,
            (_,true,Less|Equal)=>Greater,
            _=>Equal
        }
    }
    fn insert(self,l:&mut Vec<Rc<SolutionStatus<M>>>) -> Option<&mut Rc<SolutionStatus<M>>> {
        let mut j = 0;
        loop {
            if j==l.len() {l.push(Rc::new(self));return l.last_mut();}
            match self.compare_usefulness(&l[j]) {
                Less=>{return None;}
                Greater=>{l.remove(j);}
                Equal=>{j+=1;}
            }
        }
    }
    fn transfix(
        a:Transition,
        v:&Vec<Rc<SolutionStatus<M>>>,
        builder:&mut ExpressionBuilder,
        ntfa:&NTFABuilder,
        x:usize
    )->Option<SolutionStatus<M>> {
        let size = v.iter().map(|x|x.size).sum::<usize>()+1;
        // let ex = v.iter().map(|x|&x.value).collect::<Vec<_>>();
        let mapping = match v.iter().fold(if let Recursion=a {
            let mut inp = ntfa.paths[v[0].node].2.clone();
            let oup = &ntfa.paths[x].2;
            let mut buffer = Vec::new();
            while let Some((f,_)) = inp.first().copied() {
                let mut ins = Vec::new();
                inp.retain(|(z,(a,_))|if *z==f {ins.push(*a);false} else {true});
                // if ins.len()>1 {panic!("program is attempting to generate an inner disjunction, which isn't supported yet.")}
                let outs : Vec<_> = oup.iter().filter(|(z,_)|*z==f).map(|(_,(z,_))|*z).collect();
                // if outs.len()>1 {panic!("program is attempting to generate an inner disjunction, which isn't supported yet.")}
                buffer.push((ins[0],outs[0]));
            }
            M::from_vec(buffer)
        } else {Some(M::empty())},|a,x|match (a,&x.mapping) {
            (None,_)=>None,
            (Some(a),b)=>a.intersect(&b),
        }) {Some(x)=>x,None=>{return None;}};
        let mut v = v.iter().map(|x|x.dsl.clone()).collect::<Vec<_>>();
        let dsl = match a {
            Constant(x)=>BaseValue(x),
            ArbitraryFunc(w)=>ApplyStack(Box::new(BaseValue(builder.functions[w].concval)),v),
            Recursion=>ApplyStack(Box::new(RecursivePlaceholder),v),
            Switch(_)=>SwitchValue(Box::new(v.remove(0)),v),
            Input=>AccessStack(0),
            Transition::Construct(x)=>Dsl::Construct(x,v),
            Destruct(x,y)=>Deconstruct(x,y,Box::new(v.remove(0))),
        };
        Some(SolutionStatus {
            dsl,size,mapping,node:x
        })
        // if a==10 {
        //     panic!();
        //     // let biz = (0..m.len()).map(|i|{
        //     //     panic!();
        //     //     let u:Option<Vec<usize>> = ex[0][i].map(|z|m[i].recursion.get(&z).map(|x|x.iter().copied()).into_iter().flatten().collect());
        //     //     u
        //     // });
        //     // let mut cart : Vec<(_,Vec<Option<usize>>)> = vec![(mapping,Vec::new())];//I hate n-ary cartesian products
        //     // for (bin,brow) in biz.enumerate() {
        //     //     if let Some(brow) = brow {
        //     //         let mut buf = Vec::new();
        //     //         if brow.len()==0 {return Vec::new()}
        //     //         for (cmap,c) in cart {
        //     //             'defeat: for b in brow.iter() {
        //     //                 let mut cmcl = cmap.clone();
        //     //                 if *b != 0 {
        //     //                     if let Some(bex) = ex[0][bin] {
        //     //                         match &mut cmcl {
        //     //                             None=>{
        //     //                                 let mut hm=HashMap::new();
        //     //                                 hm.insert(bex,*b);
        //     //                                 cmcl=Some(Rc::new(hm));
        //     //                             },
        //     //                             Some(x)=> match Rc::make_mut(x).entry(bex) {
        //     //                                 Vacant(hole) => {hole.insert(*b);}
        //     //                                 Occupied(spot) => {
        //     //                                     if *spot.get() != *b {continue 'defeat;}
        //     //                                 }
        //     //                             }
        //     //                         }
        //     //                     }
        //     //                 }
        //     //                 let mut cl = c.clone();
        //     //                 cl.push(Some(*b));
        //     //                 buf.push((cmcl,cl));
        //     //             }
        //     //         }
        //     //         cart=buf;
        //     //     } else {
        //     //         for (_,c) in cart.iter_mut() {c.push(None);}
        //     //     }
        //     // }
        //     // for (mapping,value) in cart {
        //     //     println!("outputting!");
        //     //     result.push(SolutionStatus {
        //     //         dsl:dsl.clone(),size,value,mapping
        //     //     })
        //     // }
        // } else if a==9 {
        //     panic!()
        //     // let value:Vec<Option<usize>> = (0..m.len()).map(|i|{
        //     //     ex[0][i].and_then(|z|match &builder.values[z].0 {
        //     //         LValue(_)=>ex[1][i],
        //     //         RValue(_)=>ex[2][i],
        //     //         _=>None
        //     //     })
        //     // }).collect();
        //     // result.push(SolutionStatus {
        //     //     dsl,size,value,mapping
        //     // })
        // } else {
        //     panic!();
        //     // let value:Vec<Option<usize>> = (0..m.len()).map(|i|{
        //     //     ex.iter().map(|x|x[i]).try_fold(Vec::new(),|mut acc,x|{
        //     //         if let Some(x)=x {
        //     //             acc.push(x);Some(acc)
        //     //         } else {None}
        //     //     }).and_then(|z|m[i].remap.get(&(a,z))).copied()
        //     // }).collect();
        //     // result.push(SolutionStatus {
        //     //     dsl,size,value,mapping
        //     // })
        // }
        // result
    }

}




