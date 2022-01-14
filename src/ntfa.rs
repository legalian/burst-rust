

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::BinaryHeap;
use std::collections::hash_map::Entry::*;
use std::mem::take;
use crate::queue::{*};
use crate::dsl::{*};
use crate::nftabuilder::{*};
use crate::debug::{*};

use Dsl::{*};

struct CopyOftenLinAssoc(Vec<usize>);
impl CopyOftenLinAssoc {
    fn new()->Self {CopyOftenLinAssoc(Vec::new())}
    fn from(a:usize)->Self {CopyOftenLinAssoc(vec![a])}
    fn cons(&self,a:usize)->Self {
        let mut u=self.0.clone();
        u.push(a);
        CopyOftenLinAssoc(u)
    }
    fn get(&self,a:usize)->Option<usize> {
        self.0.iter().rev().position(|&x|x==a)
    }
}

#[derive(Debug,Clone,Hash,PartialEq,Eq,PartialOrd,Ord)]
enum NTFAref {
    DeBruijn(usize),
    Absolute(usize)
}
use NTFAref::{*};
pub struct NTFABuilder {
    paths:Vec<Vec<(usize,Vec<NTFAref>)>>,//inner vec must be sorted
    revhash:HashMap<Vec<(usize,Vec<NTFAref>)>,usize>
}
impl NTFABuilder {
    fn get_ntfa(&mut self,mut deps:Vec<(usize,Vec<NTFAref>)>)->usize {
        deps.sort_unstable();
        if (1..deps.len()).any(|i|deps[i]==deps[i - 1]) {
            panic!("there shouldn't be any duplicates here")
        }
        match self.revhash.entry(deps) {
            Occupied(x)=>{*x.get()}
            Vacant(x)=>{
                let nval=self.paths.len();
                self.paths.push(x.key().clone());
                x.insert(nval);
                nval
            }
        }
    }
    pub fn intersect(&mut self,a:usize,b:usize,
        deb:usize,
        mut debrujin_a:Vec<usize>,
        mut debrujin_b:Vec<usize>
    ) -> usize {
        debrujin_a.insert(0,a);
        debrujin_b.insert(0,b);
        // struct ArtificialStack<'a> {
        //     a:usize,
        //     b:usize,
        //     ao:usize,
        //     bo:usize,
        //     al:&'a [(usize,Vec<NTFAref>)],
        //     bl:&'a [(usize,Vec<NTFAref>)]
        // }



        let mut memo:HashMap<(usize,usize),usize> = HashMap::new();


        // let debrujin_a:HashMap<usize,usize> = HashMap::new();
        // let debrujin_b:HashMap<usize,usize> = HashMap::new();
        // let deb = 0;

        let mut al = &self.paths[a];
        let mut bl = &self.paths[b];
        let mut a=0;
        let mut b=0;
        let mut ao;
        let mut bo;
        let mut output = Vec::new();
        while a<al.len() && b<bl.len() {
            if al[a].0<bl[b].0 {a+=1;}
            else if al[a].0>bl[b].0 {b+=1;}
            else {
                let f=al[a].0;
                ao=0;
                bo=0;
                while a+ao<al.len() && al[a+ao].0==f {
                    bo=0;
                    while b+bo<bl.len() && bl[b+bo].0==f {
                        //output (f,)
                        let mut res = Vec::new();
                        for i in 0..al[a+ao].1.len() {
                            let ar = match al[a+ao].1[i] {Absolute(x)=>x,DeBruijn(x)=>debrujin_a[x]};
                            let br = match bl[b+bo].1[i] {Absolute(x)=>x,DeBruijn(x)=>debrujin_b[x]};
                            if let Some(z) = memo.get(&(ar,br)) {res.push(DeBruijn(*z));continue;}
                            let z = self.intersect(
                                ar,br,deb+1,
                                debrujin_a.clone(),
                                debrujin_b.clone()
                            );
                            al = &self.paths[a];
                            bl = &self.paths[b];
                            memo.insert((ar,br),deb);//this part needs to change...
                            res.push(Absolute(z));
                        }
                        output.push((f,res));
                        bo+=1;
                    }
                    ao+=1;
                }
                a+=ao;
                b+=bo;
            }
        }
        self.get_ntfa(output)
    }
    pub fn unroll(&mut self,a:usize,r:usize)->Vec<(usize,Vec<NTFAref>)> {
        let output:Vec<(usize,Vec<NTFAref>)> = Vec::new();
        for (f,a) in self.paths[a] {
            let row:Vec<NTFAref> = Vec::new();
            for b in a {
                row.push(match b {
                    DeBruijn(0)=>Absolute(r),
                    DeBruijn(w)=>DeBruijn(w-1),
                    Absolute(c)=>{
                        let s1 = self.unroll(c,r);
                        Absolute(self.get_ntfa(s1))
                    }
                });
            }
            // output.push(f,)
        }
        output
    }
    pub fn union(&mut self,mut a:Vec<usize>) -> Option<usize> {
        if a.len()==0 {return None}
        if a.len()==1 {return Some(a.remove(0))}
        panic!("TODO")
    }
}


pub type NTFA = usize;

pub struct PartialNTFA {
    rules:HashMap<usize,Vec<(usize,Vec<usize>)>>
}
impl PartialNTFA {
    pub fn new()->Self {PartialNTFA{rules:HashMap::new()}}
    pub fn add_rule(&mut self,f:usize,a:Vec<usize>,r:usize) {
        self.rules.entry(r).or_default().push((f,a));
    }
    pub fn convert(self,builder:&mut NTFABuilder,accstates:&HashSet<usize>)->HashSet<NTFA> {
        struct ArtificialStack<'a> {
            layercache: HashMap<usize,usize>,
            debrujin: CopyOftenLinAssoc,
            outercollect: Vec<(usize,Vec<NTFAref>)>,
            innercollect: Vec<NTFAref>,
            outertrav:&'a [(usize,Vec<usize>)],
            innertrav:&'a [usize],
            innertoken: usize,
        }
        let mut stack:Vec<ArtificialStack> = Vec::new();
        let mut accepting:HashSet<usize> = HashSet::new();
        for acc in accstates {
            if let Some(y) = self.rules.get(acc) {
                stack.push(ArtificialStack{
                    layercache:HashMap::new(),
                    debrujin:CopyOftenLinAssoc::from(*acc),
                    outercollect:Vec::new(),
                    innercollect:Vec::new(),
                    outertrav:&y[1..],
                    innertrav:&y[0].1,
                    innertoken:y[0].0
                });
            } else {continue;}
            while let Some(x) = stack.last_mut() {
                loop {
                    if let Some(y) = x.layercache.get(&x.innertrav[0]).map(|x|Absolute(*x))
                        .or_else(||x.debrujin.get(x.innertrav[0]).map(|x|DeBruijn(x))) {
                        x.innercollect.push(y);
                        if x.innertrav.len()>1 {
                            x.innertrav=&x.innertrav[1..];
                            continue;
                        } else {
                            let v = take(&mut x.innercollect);
                            x.outercollect.push((x.innertoken,v));
                        }
                    } else {
                        if let Some(y) = self.rules.get(&x.innertrav[0]) {
                            let bb = x.debrujin.cons(x.innertrav[0]);
                            stack.push(ArtificialStack{
                                layercache:HashMap::new(),
                                debrujin:bb,
                                outercollect:Vec::new(),
                                innercollect:Vec::new(),
                                outertrav:&y[1..],
                                innertrav:&y[0].1,
                                innertoken:y[0].0
                            });
                            break;
                        } else {
                            x.innercollect.clear();
                        }
                    }
                    if x.outertrav.len()>1 {
                        x.innertoken=x.outertrav[0].0;
                        x.innertrav=&x.outertrav[0].1;
                        x.outertrav=&x.outertrav[1..];
                    } else {
                        let z = builder.get_ntfa(stack.pop().unwrap().outercollect);
                        if let Some(x) = stack.last_mut() {
                            x.layercache.insert(x.innertrav[0],z);
                        } else {
                            accepting.insert(z);
                        }
                        break;
                    }
                }
            }
        }
        accepting
    }
}


// pub struct NTFA {
//     // pub nullary:HashMap<usize,HashSet<usize>>,
//     // pub rules:HashMap<usize,HashMap<usize,HashSet<Vec<usize>>>>
// }
// impl NTFA {
//     pub fn new()->NTFA {
//         NTFA {
//             nullary:HashMap::new(),
//             rules:HashMap::new()
//         }
//     }
//     pub fn add_nullary(&mut self,f:usize,s:usize) {
//         self.nullary.entry(f).or_default().insert(s);
//     }
//     pub fn add_rule(&mut self,f:usize,a0:usize,rest:Vec<usize>) {
//         self.rules.entry(a0).or_default().entry(f).or_default().insert(rest);
//     }
// }

// fn disjoint_union(mut a:HashMap<usize,usize>,b:HashMap<usize,usize>) -> Option<HashMap<usize,usize>> {
//     for (k,v) in b.into_iter() {
//         match a.entry(k) {
//             Vacant(hole) => {hole.insert(v);}
//             Occupied(spot) => {
//                 if *spot.get() != v {return None;}
//             }
//         }
//     } Some(a)
// }
// fn disjoint_union_3(a:HashMap<usize,usize>,b:HashMap<usize,usize>,c:HashMap<usize,usize>) -> Option<HashMap<usize,usize>> {
//     disjoint_union(a,b).and_then(|x|disjoint_union(x,c))
// }

// impl NTFA {
//     pub fn trim(&mut self,states:&HashSet<usize>) {
//         let mut nullary : HashMap<usize,Vec<usize>> = HashMap::new();
//         let mut totalset : HashMap<usize,Vec<(usize,Vec<usize>,usize)>> = HashMap::new();//final:(a0,an,f,index)
//         let mut queue : VecDeque<usize> = VecDeque::new();
//         for (f,rs) in self.nullary.iter() {
//             for r in rs {
//                 nullary.entry(*r).or_default().push(*f);
//             }
//         }
//         for (a0,rest1) in self.rules.iter() {
//             for (f,rest2) in rest1.iter() {
//                 for an in rest2.iter() {
//                     totalset.entry(an[an.len()-1]).or_default().push((*a0,an.clone(),*f));
//                 }
//             }
//         }
//         for state in states.iter() {
//             queue.push_back(*state);
//         }
//         while let Some(x) = queue.pop_front() {
//             nullary.remove(&x);
//             if let Some(y) = totalset.remove(&x) {
//                 for (a0,an,_) in y {
//                     queue.push_back(a0);
//                     for a in an {queue.push_back(a);}
//                 }
//             }
//         }
//         for (_,removals) in nullary.iter() {
//             for r in removals {
//                 if if let Some(x) = self.nullary.get_mut(r)
//                 {x.remove(&r);x.len()==0} else {false} {
//                     self.nullary.remove(r);
//                 }
//             }
//         }
//         for (_,removals) in totalset.into_iter() {
//             for (a0,an,f) in removals.iter() {
//                 let ma = self.rules.get_mut(&a0).unwrap();
//                 let mf = ma.get_mut(&f).unwrap();
//                 mf.remove(an);
//                 if mf.len()==0 {
//                     ma.remove(&f);
//                     if ma.len()==0 {
//                         self.rules.remove(&a0);
//                     }
//                 }
//             }
//         }
//     }
//     pub fn accepting_run(
//         &self,
//         map:&Option<HashMap<usize,Vec<usize>>>,
//         accepting:&HashSet<usize>,
//         ex:&mut ExpressionBuilder
//     ) -> Option<(Dsl,usize,HashMap<usize,usize>)> {
//         let mut queue : BinaryHeap<QueueElem<(usize,Dsl,Rc<HashMap<usize,usize>>)>> = BinaryHeap::new();
//         let mut extended_memo:HashMap<usize,Vec<(usize,usize,usize,&[usize])>> = HashMap::new();
//         let baseline_map = Rc::new(HashMap::new());
//         for (token,states) in self.nullary.iter() {
//             for state in states {
//                 if *token==0 {//unit
//                     queue.push(QueueElem{item:(*state,BaseValue(1),baseline_map.clone()),priority:0});
//                 } else if *token==1 {//input
//                     queue.push(QueueElem{item:(*state,AccessStack(0),baseline_map.clone()),priority:0});
//                 } else {panic!("unknown nullary func")}
//             }
//         }
//         let mut hm:HashMap<usize,(Dsl,usize,Rc<HashMap<usize,usize>>)> = HashMap::new();
//         while let Some(QueueElem{item:(state,dsl,states),priority:size}) = queue.pop() {
//             if hm.contains_key(&state) {continue;}
//             if accepting.contains(&state) {return Some((dsl,size,(*states).clone()));}
//             hm.insert(state,(dsl.clone(),size,states.clone()));
//             let mut fromr:Vec<(usize, usize, usize, &[usize])>=Vec::new();
//             if let Some(ad) = self.rules.get(&state) {
//                 for (f,av) in ad {
//                     for v in av {
//                         let last = v[v.len()-1];
//                         if state==last || v[..v.len()-1].contains(&last) {continue;}
//                         fromr.push((*f,0,state,v));
//                     }
//                 }
//             }
//             'outloop: for (f,mut i,v0,v) in extended_memo.remove(&state).into_iter().flatten().chain(fromr.into_iter()) {
//                 if hm.contains_key(&v[v.len()-1]) {continue;}
//                 while i+1<v.len() {
//                     if !hm.contains_key(&v[i]) {
//                         extended_memo.entry(v[i]).or_default().push((f,i+1,v0,v));
//                         continue 'outloop;
//                     }
//                     i+=1;
//                 }
//                 match f {
//                     3=>{queue.push(QueueElem{item:(v[0],ex.get_left_value(dsl.clone()),states.clone()),priority:size+1});}
//                     4=>{queue.push(QueueElem{item:(v[0],ex.get_right_value(dsl.clone()),states.clone()),priority:size+1});}
//                     5=>{queue.push(QueueElem{item:(v[0],ex.get_l_prog(dsl.clone()),states.clone()),priority:size+1});}
//                     6=>{queue.push(QueueElem{item:(v[0],ex.get_r_prog(dsl.clone()),states.clone()),priority:size+1});}
//                     7=>{queue.push(QueueElem{item:(v[0],ex.get_undo_left(dsl.clone()),states.clone()),priority:size+1});}
//                     8=>{queue.push(QueueElem{item:(v[0],ex.get_undo_right(dsl.clone()),states.clone()),priority:size+1});}
//                     10=>{
//                         let mut bruh = (*states).clone();
//                         match map {
//                             Some(x) => {
//                                 for (inp,oup) in x[&state].iter().zip(x[&v[0]].iter()) {
//                                     match bruh.entry(*inp) {
//                                         Vacant(hole) => {hole.insert(*oup);}
//                                         Occupied(spot) => {if *spot.get() != *oup {continue 'outloop;}}
//                                     }
//                                 }
//                             }
//                             None => match bruh.entry(state) {
//                                 Vacant(hole) => {hole.insert(v[0]);}
//                                 Occupied(spot) => {if *spot.get() != v[0] {continue 'outloop;}}
//                             }
//                         }
//                         queue.push(QueueElem{item:(
//                             v[0],
//                             ApplyStack(Box::new(AccessStack(1)),vec![dsl.clone()]),
//                             states.clone()
//                         ),priority:size+1})
//                     }
//                     2=>{//different assumptions here onwards... non-unary functions can't use states or state or dsl or size
//                         let (av,asiz,ssa) = hm[&v0].clone();
//                         let (bv,bsiz,ssb) = hm[&v[0]].clone();
//                         let disj = match disjoint_union((*ssa).clone(),(*ssb).clone()) {
//                             Some(x)=>x,
//                             None=>{continue 'outloop;}
//                         };
//                         queue.push(QueueElem{item:(
//                             v[1],
//                             Pair(Box::new(av),Box::new(bv)),
//                             Rc::new(disj)
//                         ),priority:asiz+bsiz+1});
//                     }
//                     9=>{
//                         let (av,asiz,ssa) = hm[&v0].clone();
//                         let (bv,bsiz,ssb) = hm[&v[0]].clone();
//                         let (cv,csiz,ssc) = hm[&v[1]].clone();
//                         let disj = match disjoint_union_3((*ssa).clone(),(*ssb).clone(),(*ssc).clone()) {
//                             Some(x)=>x,
//                             None=>{continue 'outloop;}
//                         };
//                         queue.push(QueueElem{item:(
//                             v[2],
//                             SwitchValue(Box::new(av),Box::new(bv),Box::new(cv.clone())),
//                             Rc::new(disj)
//                         ),priority:asiz+bsiz+csiz+1});
//                     }
//                     w=>{
//                         let mut siz = 1;
//                         let mut ss = None;
//                         let mut j = Vec::new();
//                         for x in once(&v0).chain(v.iter()) {
//                             let (jn,s,snew) = hm[x].clone();
//                             siz+=s;
//                             ss = match ss {
//                                 None=>Some((*snew).clone()),
//                                 Some(ss)=>Some(match disjoint_union(ss,(*snew).clone()) {
//                                     Some(x)=>x,
//                                     None=>{continue 'outloop;}
//                                 })
//                             };
//                             j.push(jn);
//                         }
//                         queue.push(QueueElem{item:(
//                             *v.last().unwrap(),
//                             ApplyStack(Box::new(BaseValue(ex.get_f_handle(w-11))),j),
//                             Rc::new(ss.unwrap())
//                         ),priority:siz});
//                     }
//                 }
//             }
//         } None
//     }
// }

// //new ntfa needs to be on the left
// //new value, accumulator
// pub fn combine_on_right(mut a:HashMap<usize,Vec<usize>>,b:HashMap<usize,Vec<usize>>)->HashMap<usize,Vec<usize>> {
//     for a in a.values_mut() {
//         let ap = a.pop().unwrap();
//         a.extend(b[&ap].iter().copied());
//     } a
// }







// struct IntersectionProblem<'a> {
//     a : &'a NTFA,
//     b : &'a NTFA,
//     a_accepting : &'a HashSet<usize>,
//     b_accepting : &'a HashSet<usize>,
//     queue : VecDeque<(usize,usize,usize)>,
//     a_to_b : HashMap<usize,HashMap<usize,usize>>,
//     b_to_c : HashMap<usize,HashMap<(usize,Vec<usize>),HashSet<&'a [usize]>>>,
//     c_to_a : HashMap<(usize,Vec<usize>),HashMap<usize,HashSet<&'a [usize]>>>,
//     states : usize,
//     result : NTFA,
//     result_accepting : HashSet<usize>
// }
// impl<'a> IntersectionProblem<'a> {
//     fn new(a:&'a NTFA,a_accepting:&'a HashSet<usize>,b:&'a NTFA,b_accepting:&'a HashSet<usize>)->IntersectionProblem<'a> {
//         IntersectionProblem {
//             a,b,
//             a_accepting,b_accepting,
//             queue:VecDeque::new(),
//             a_to_b:HashMap::new(),b_to_c:HashMap::new(),c_to_a:HashMap::new(),
//             result:NTFA {
//                 nullary:HashMap::new(),rules:HashMap::new()
//             },
//             result_accepting:HashSet::new(),
//             states:0
//         }
//     }
//     fn populate_queue(&mut self) {
//         for (k,vas) in self.a.nullary.iter() {
//             if let Some(vbs) = self.b.nullary.get(&k) {
//                 for va in vas {
//                     for vb in vbs {
//                         let newvar = self.get_variable(*va,*vb);
//                         self.result.nullary.entry(*k).or_default().insert(newvar);
//                     }
//                 }
//             }
//         }
//     }
//     fn get_variable(&mut self,a:usize,b:usize)->usize {
//         match self.a_to_b.entry(a).or_insert(HashMap::new()).entry(b) {
//             Occupied(x)=>*x.get(),
//             Vacant(x)=>{
//                 if self.a_accepting.contains(&a) && self.b_accepting.contains(&b) {
//                     self.result_accepting.insert(self.states);
//                 }
//                 self.queue.push_back((a,b,self.states));
//                 x.insert(self.states);
//                 self.states+=1;
//                 self.states-1
//             }
//         }
//     }
//     fn solve(mut self)->(NTFA,HashSet<usize>,HashMap<usize,Vec<usize>>) {
//         self.populate_queue();
//         while let Some((aside,bside,nvarn)) = self.queue.pop_front() {
//             let mut innerqueue : VecDeque<(HashSet<&'a [usize]>,HashSet<&'a [usize]>,usize,Vec<usize>)> = VecDeque::new();
//             if let Some(inter_c) = self.b_to_c.get(&bside) {
//                 for (c,lines_b) in inter_c.iter() {
//                     if let Some(inter_a) = self.c_to_a.get(c) {
//                         if let Some(lines_a) = inter_a.get(&aside) {
//                             innerqueue.push_back((lines_a.clone(),lines_b.clone(),c.0,c.1.iter().cloned().chain(once(nvarn)).collect()));
//                             check(innerqueue.back().unwrap());
//                         }
//                     }
//                 }
//             }
//             if let (Some(ad),Some(bd)) = (self.a.rules.get(&aside),self.b.rules.get(&bside)) {
//                 for (k,av) in ad {
//                     if let Some(bv) = bd.get(k) {
//                         if av.iter().next().unwrap().len()==1 {//len(av[0])==1 implies len(av)==1 only for DTFAs, but angelic execution deals in NTFAs.
//                             for x in av.iter() {
//                                 for y in bv.iter() {
//                                     let newvarname = self.get_variable(x[0],y[0]);
//                                     self.result.rules.entry(nvarn).or_default().entry(*k).or_default().insert(vec![newvarname]);
//                                 }
//                             }
//                         } else {
//                             let av_int : HashSet<&[usize]> = av.iter().map(|x|x.as_slice()).collect();
//                             let bv_int : HashSet<&[usize]> = bv.iter().map(|x|x.as_slice()).collect();
//                             innerqueue.push_back((av_int,bv_int,*k,vec![nvarn]));
//                             check(innerqueue.front().unwrap());
//                         }
//                     }
//                 }
//             }
//             while let Some((av,bv,cf,newnvarnvec)) = innerqueue.pop_front() {
//                 if av.iter().next().unwrap().len()==1 {
//                     for x in av.iter() {
//                         for y in bv.iter() {
//                             let newvarname = self.get_variable(x[0],y[0]);
//                             self.result.rules.entry(newnvarnvec[0]).or_default().entry(cf).or_default().insert(
//                                 newnvarnvec.iter().skip(1).cloned().chain(once(newvarname)).collect()
//                             );
//                         }
//                     }
//                     continue
//                 }
//                 let ca_line = self.c_to_a.entry((cf,newnvarnvec.clone())).or_default();
//                 for a in av {
//                     if ca_line.entry(a[0]).or_default().insert(&a[1..]) {
//                         if let Some(inter_b) = self.a_to_b.get(&a[0]) {
//                             for (b,newtag) in inter_b.iter() {
//                                 if let Some(inter_c) = self.b_to_c.get(b) {
//                                     if let Some(otherlines) = inter_c.get(&(cf,newnvarnvec.clone())) {
//                                         innerqueue.push_back((
//                                             {let mut hs = HashSet::new();hs.insert(&a[1..]);hs},
//                                             otherlines.clone(),
//                                             cf,
//                                             newnvarnvec.iter().cloned().chain(once(*newtag)).collect()
//                                         ));
//                                         check(innerqueue.back().unwrap());
//                                     }
//                                 }
//                             }
//                         }
//                     }
//                 }
//                 for b in bv {
//                     if self.b_to_c.entry(b[0]).or_default().entry((cf,newnvarnvec.clone())).or_default().insert(&b[1..]) {
//                         for (a,otherlines) in ca_line.iter() {
//                             if let Some(ca_line) = self.a_to_b.get(a) {
//                                 if let Some(newtag) = ca_line.get(&b[0]) {
//                                     innerqueue.push_back((
//                                         otherlines.clone(),
//                                         {let mut hs = HashSet::new();hs.insert(&b[1..]);hs},
//                                         cf,
//                                         newnvarnvec.iter().cloned().chain(once(*newtag)).collect()
//                                     ));
//                                     check(innerqueue.back().unwrap());
//                                 }
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//         self.result.trim(&self.result_accepting);
//         let mut statemap = HashMap::new();
//         for (a,bc) in self.a_to_b.into_iter() {
//             for (b,c) in bc.into_iter() {
//                 statemap.insert(c,vec![a,b]);
//             }
//         }
//         (self.result,self.result_accepting,statemap)
//     }
// }
// pub fn intersection(a:&NTFA,a_accepting:&HashSet<usize>,b:&NTFA,b_accepting:&HashSet<usize>) -> (NTFA,HashSet<usize>,HashMap<usize,Vec<usize>>) {
//     IntersectionProblem::new(a,a_accepting,b,b_accepting).solve()
// }



// fn check((av,bv,cf,newnvarnvec):&(HashSet<&[usize]>,HashSet<&[usize]>,usize,Vec<usize>)) {
//     if let Some(debug) = debug_expectedlen(*cf) {
//         for a in av {
//             assert!(debug == a.len()+newnvarnvec.len()-1);
//         }
//         for b in bv {
//             assert!(debug == b.len()+newnvarnvec.len()-1);
//         }
//     }
// }

