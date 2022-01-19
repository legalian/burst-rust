

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::collections::BinaryHeap;
use std::collections::hash_map::Entry::*;
use std::rc::Rc;
use std::mem::take;
use crate::dsl::{*};
use crate::nftabuilder::{*};
// use crate::debug::{*};
// use crate::queue::{*};
use std::cmp::Ordering;
use Ordering::{*};
use Dsl::{*};


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
fn disjoint_union_3(a:HashMap<usize,usize>,b:HashMap<usize,usize>,c:HashMap<usize,usize>) -> Option<HashMap<usize,usize>> {
    disjoint_union(a,b).and_then(|x|disjoint_union(x,c))
}

pub struct NTFABuilder {
    paths:Vec<Vec<(usize,Vec<usize>)>>,//inner vec must be sorted
    revhash:HashMap<Vec<(usize,Vec<usize>)>,usize>,
    intersect_memo:HashMap<(usize,usize),usize>
}
impl NTFABuilder {
    pub fn new()->Self {
        NTFABuilder {
            paths:Vec::new(),//inner vec must be sorted
            revhash:HashMap::new(),
            intersect_memo:HashMap::new()
        }
    }
    fn get_ntfa(&mut self,mut deps:Vec<(usize,Vec<usize>)>)->usize {
        deps.sort_unstable();
        deps.dedup();
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
    fn get_placeholder(&mut self)->usize {
        self.paths.push(vec![]);
        self.paths.len()-1
    }
    fn insert_into_placeholder(&mut self,mut deps:Vec<(usize,Vec<usize>)>,i:usize) {
        deps.sort_unstable();
        deps.dedup();
        self.revhash.insert(deps.clone(),i);
        self.paths[i]=deps;
    }

    pub fn intersect(&mut self,a_start:usize,b_start:usize) -> Option<usize> {
        let place=self.get_placeholder();
        self.intersect_memo.insert((a_start,b_start),place);

        let mut al = &self.paths[a_start];
        let mut bl = &self.paths[b_start];
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
                        let mut res = Vec::new();
                        let mut valid=true;
                        for i in 0..al[a+ao].1.len() {
                            let ar = al[a+ao].1[i];
                            let br = bl[b+bo].1[i];
                            if ar==br {
                                res.push(ar);
                                continue
                            }
                            if let Some(z) = self.intersect_memo.get(&(ar,br)) {
                                res.push(*z);
                                continue
                            }
                            let z = self.intersect(ar,br);
                            al = &self.paths[a_start];
                            bl = &self.paths[b_start];
                            if let Some(z) = z {
                                res.push(z);
                            } else {
                                valid=false;
                                break;
                            }
                        }
                        if valid {
                            output.push((f,res));
                        }
                        bo+=1;
                    }
                    ao+=1;
                }
                a+=ao;
                b+=bo;
            }
        }
        if output.len()==0 {return None}
        self.insert_into_placeholder(output,place);
        Some(place)
    }
    pub fn union(&mut self,mut a:Vec<usize>) -> Option<usize> {
        if a.len()==0 {return None}
        if a.len()==1 {return Some(a.remove(0))}
        let mut total:Vec<(usize,Vec<usize>)> = Vec::new();
        for b in a {total.extend(self.paths[b].clone());}
        Some(self.get_ntfa(total))
    }
    pub fn get_accepting_run(
        &self,
        start:usize,
        builder:&mut ExpressionBuilder,
        map:&[ValueMapper]
    ) -> Vec<(Dsl,usize,HashMap<usize,usize>)> {
        let mut queue : BinaryHeap<SolutionStatusWrap> = BinaryHeap::new();
        queue.push(DownElem(start,0));
        let mut solns : HashMap<usize,Vec<Rc<SolutionStatus>>> = HashMap::new();
        let mut working : HashMap<usize,Vec<(&[usize],Vec<Rc<SolutionStatus>>,usize)>> = HashMap::new();
        let mut visited : HashSet<usize> = HashSet::new();
        while let Some(x) = queue.pop() {
            match x {
                DownElem(x,minsize)=>{
                    if !visited.insert(x) {continue;}
                    let y = &self.paths[x];
                    if let Some((f,_)) = y.iter().find(|(_,x)|x.len()==0) {
                        for sol in SolutionStatus::transfix(*f,&vec![],map,builder) {
                            queue.push(UpElem(x,minsize+sol.size,sol));
                        }
                    } else {
                        for (f,l) in y.iter() {
                            if l.contains(&x) {continue;}
                            queue.push(DownElem(l[0],minsize+1));
                            let mut stack = vec![(&l,Vec::<Rc<SolutionStatus>>::new(),*f)];
                            while let Some((l,v,f)) = stack.pop() {
                                if l.len()==0 {
                                    for sol in SolutionStatus::transfix(f,&v,map,builder) {
                                        queue.push(UpElem(x,minsize+sol.size,sol));
                                    }
                                }
                                working.entry(l[0]).or_default().push((&l[1..],v,f));

                            }
                            // while l.len()>0 {
                            //     l[0]
                            // }

                        }
                    }
                }
                UpElem(x,minsize,sol)=>{
                    if !sol.insert(solns.entry(x).or_default()) {continue;}
                    // for (l,v,f) in working.get(&x).into_iter().flatten().collect::<Vec<_>>() {
                    //     let l=*l; let f=*f;
                    //     if l.len()>0 {
                    //         working.entry(l[0]).or_default().push((l,vec![],f));

                    //     } else {

                    //     }

                    // }
                }
            }
            // let new_working = match working.entry(x) {
            //     Occupied(_)=>{continue;}
            //     Vacant(x)=>{x.insert(vec![])}
            // };
            // let y = &self.paths[x];
            // if let Some((f,_)) = y.iter().find(|(_,x)|x.len()==0) {
            //     SolutionStatus::transfix(*f,&vec![],map,builder);
            // } else {
            //     for (f,z) in y.iter() {
            //         if z.contains(&x) {continue;}
            //         outerqueue.push_back(z[0]);
            //         new_working.push((z,vec![],*f));
            //     }
            // }

            // while let Some(SolutionStatusWrap(x,sol)) = innerqueue.pop() {
            //     if !sol.insert(solns.entry(x).or_default()) {continue;}
            //     'outloop: for (v,f,mut i) in working.get(&x).into_iter().flatten().copied().collect::<Vec<_>>() {
            //         while i+1<v.len() {
            //             if !solns.contains_key(&v[i]) {
            //                 working.entry(v[i]).or_default().push((v,f,i+1));
            //                 continue 'outloop;
            //             }
            //             i+=1;
            //         }
            //     }
            // }
        }


        solns.remove(&start).unwrap_or_default().into_iter().map(|x|{
            let SolutionStatus{dsl:a,size:b,mapping:c,..} = &*x;
            (a.clone(),*b,c.as_ref().map(|x|(**x).clone()).unwrap_or_default())
        }).collect()

        //rephrase hm:
        //    the smallest value to construct <> given that states <>,<>, and <> are irrelevant to you
        //if you have an answer for X where [a,b] are irrelevant, it'll work even if [a,b,c] are irrelevant to you.
        //if you set out to construct X where [a,b] are irrelevant, but you don't use a, then you have X where [b] is irrelevant.
        //if you have a unary answer, nothing is considered irrelevant.

        //if you have an answer for X where [a,b] is irrelevant, and you have that [a] is irrelevant, redo it.
        

        //[a] is specifically ignored for a memo entry if any children ignored it or if you did

        //anything memo entry ignoring something that isn't in your stack -> dump/destroy

    //     struct ArtificialStack<'a> {
    //         currentbest: Vec<SolutionStatus>,
    //         stackrequirement: HashSet<usize>,
    //         innercollect: Vec<Vec<SolutionStatus>>,
    //         outertrav:&'a [(usize,Vec<usize>)],
    //         innertrav:&'a [usize],
    //         innertoken: usize,
    //         place:usize,

    //         // hadperfect:bool
    //     }
    //     let y = &self.paths[start];
    //     println!("adding {} to the stack",start);
    //     let mut stack:Vec<ArtificialStack> = vec![ArtificialStack{
    //         currentbest:Vec::new(),
    //         stackrequirement:HashSet::new(),
    //         innercollect:Vec::new(),
    //         outertrav:&y[1..],
    //         innertrav:&y[0].1,
    //         innertoken:y[0].0,
    //         // hadperfect:false,
    //         place:start
    //     }];
    //     let mut hm:HashMap<usize,Option<(HashSet<usize>,Vec<SolutionStatus>)>> = HashMap::new();
    //     hm.insert(start,None);
    //     while let Some(x) = stack.last_mut() {
    //         'sloop: loop {
    //             if x.innertrav.len()>0 {
    //                 match hm.get(&x.innertrav[0]) {
    //                     Some(Some((r,s))) => {
    //                         for required in r {
    //                             if *required != x.place {
    //                                 if hm[required].is_some() {
    //                                     // println!("I aborted because the child was disregarding: {}",required);
    //                                     hm.remove(&x.innertrav[0]);
    //                                     break 'sloop;
    //                                 }
    //                             }
    //                         }
    //                         for required in r {
    //                             if *required != x.place {
    //                                 x.stackrequirement.insert(*required);
    //                             }
    //                         }
    //                         if s.len()>0 {
    //                             x.innercollect.push(s.clone());
    //                             x.innertrav=&x.innertrav[1..];
    //                             continue;
    //                         } else {
    //                             // panic!();
    //                             x.innercollect.clear();
    //                             x.innertrav=&[];
    //                         }
    //                     }
    //                     None=>{
    //                         let ind = x.innertrav[0];
    //                         let y = &self.paths[ind];
    //                         hm.insert(ind,None);
    //                         println!("adding {} to stack.",ind);
    //                         stack.push(ArtificialStack{
    //                             currentbest:Vec::new(),
    //                             stackrequirement:HashSet::new(),
    //                             innercollect:Vec::new(),
    //                             outertrav:&y[1..],
    //                             innertrav:&y[0].1,
    //                             innertoken:y[0].0,
    //                             place:ind,
    //                             // hadperfect:false
    //                         });
    //                         break;
    //                     }
    //                     Some(None)=>{
    //                         if x.innertrav[0] != x.place {
    //                             x.stackrequirement.insert(x.innertrav[0]);
    //                         }
    //                         // println!("RULE DEEMED UNSATISFIABLE BECAUSE OF A LOOP {:?}",hm.get(&x.innertrav[0]).map(|x|x.as_ref().map(|_|5)));
    //                         x.innercollect.clear();
    //                         x.innertrav=&[];
    //                     }
    //                 }
    //             } else {
    //                 let v = take(&mut x.innercollect);
    //                 if start == x.place {
    //                     println!("transfixing once {}",x.innertoken);
    //                 }
    //                 for newsol in SolutionStatus::transfix(x.innertoken,&v,map,builder) {
    //                     if start == x.place {
    //                         println!("found solution of size {}",newsol.size);
    //                     }
    //                     newsol.insert(&mut x.currentbest);
    //                 }
    //                 if x.innertoken==0 || x.innertoken==1 {
    //                     // x.hadperfect=true;
    //                     x.outertrav=&[];//0 and 1 are both unary tokens that don't modify assignments so aborting here is safe but not required
    //                 }//they also get sorted to the top of the list naturally
    //             }
    //             if x.outertrav.len()>1 {
    //                 x.innertoken=x.outertrav[0].0;
    //                 x.innertrav=&x.outertrav[0].1;
    //                 x.outertrav=&x.outertrav[1..];
    //             } else {
    //                 let ff = stack.pop().unwrap();
    //                 println!("popping {} off of the stack with {:#?} solutions.",ff.place,ff.currentbest);
    //                 // if ff.hadperfect && (ff.currentbest.len()!=1 || ff.currentbest[0].size != 1) {
    //                 //     panic!("what the hell")
    //                 // }
    //                 hm.insert(ff.place,Some((ff.stackrequirement,ff.currentbest)));
    //                 break;
    //             }
    //         }

    //         for j in stack.iter() {
    //             if hm[&j.place].is_some() {
    //                 panic!()
    //             }
    //         }
    //     }
    //     hm.remove(&start).unwrap().unwrap().1.into_iter().map(|SolutionStatus{dsl:a,size:b,mapping:c,..}|
    //         (a,b,take(Rc::make_mut(&mut c.unwrap_or_default())))
    //     ).collect()



    }
}



#[derive(Clone,Debug)]
pub struct SolutionStatus {
    dsl:Dsl,
    size:usize,
    value:Vec<usize>,
    mapping:Option<Rc<HashMap<usize,usize>>>
}
pub enum SolutionStatusWrap {
    UpElem(usize,usize,SolutionStatus),
    DownElem(usize,usize),
}
use SolutionStatusWrap::{*};
impl SolutionStatusWrap {
    fn priority(&self)->usize {
        match self {
            UpElem(_,a,_)=>*a,
            DownElem(_,a)=>*a
        }
    }
}
impl Eq for SolutionStatusWrap {}
impl Ord for SolutionStatusWrap {
    fn cmp(&self, other: &Self) -> Ordering {
        other.priority().cmp(&self.priority())
    }
}
impl PartialOrd for SolutionStatusWrap {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(other.priority().cmp(&self.priority()))
    }
}
impl PartialEq<SolutionStatusWrap> for SolutionStatusWrap {
    fn eq(&self, other: &Self) -> bool {
        self.priority() == other.priority()
    }
}
impl SolutionStatus {
    fn compare_usefulness(&self,other:&SolutionStatus)->Ordering {
        let SolutionStatus{size:s,mapping:m,..} = other;
        match (if let Some(z)=m {//present subset of inserting
            if let Some(xx)=&self.mapping {z.iter().all(|(k,v)|xx.get(k)==Some(v))}
            else {false}
        } else {true},
        if let Some(z)=&self.mapping {//inserting subset of present
            if let Some(xx)=m {z.iter().all(|(k,v)|xx.get(k)==Some(v))}
            else {false}
        } else {true},self.size.cmp(s)) {
            // (false,_,_)(_,false,_)|=>panic!(),
            (true,_,Greater|Equal)=>Less,
            (_,true,Less|Equal)=>Greater,
            _=>Equal
        }
    }
    fn insert(self,l:&mut Vec<Rc<SolutionStatus>>) -> bool {
        let mut j = 0;
        loop {
            if j==l.len() {l.push(Rc::new(self));return true;}
            match self.compare_usefulness(&l[j]) {
                Less=>{return false;}
                Greater=>{l.remove(j);}
                Equal=>{j+=1;}
            }
        }
    }
    fn transfix(
        a:usize,
        v:&Vec<Vec<Rc<SolutionStatus>>>,
        m:&[ValueMapper],
        builder:&mut ExpressionBuilder
    )->Vec<SolutionStatus> {
        let mut perl = vec![(Vec::new(),1,Vec::new(),None)];
        for vrow in v {
            let mut buff = Vec::new();
            for (sof,size,ex,map) in perl {
                for SolutionStatus{dsl:jdsl,value:l,size:jsize,mapping:jmap} in vrow.iter().map(|x|&**x) {
                    if let Some(rmap) = match (jmap.clone(),map.clone()) {
                        (None,None)=>Some(None),
                        (Some(x),None)|(None,Some(x))=>Some(Some(x)),
                        (Some(mut x),Some(mut y))=>disjoint_union(
                            take(Rc::make_mut(&mut x)),
                            take(Rc::make_mut(&mut y))
                        ).map(|x|Some(Rc::new(x)))
                    } {
                        let mut nsof = sof.clone();
                        nsof.push(jdsl);
                        let mut nex = ex.clone();
                        nex.push(l);
                        buff.push((nsof,size+jsize,nex,rmap));
                    }
                }
            }
            perl = buff;
        }
        let mut result = Vec::new();
        'sol: for (v,size,ex,mapping) in perl {
            let dsl = match a {
                0=>BaseValue(1),
                1=>AccessStack(0),
                2=>Pair(Box::new(v[0].clone()),Box::new(v[1].clone())),
                3=>builder.get_left_value(v[0].clone()),
                4=>builder.get_right_value(v[0].clone()),
                5=>builder.get_l_prog(v[0].clone()),
                6=>builder.get_r_prog(v[0].clone()),
                7=>builder.get_undo_left(v[0].clone()),
                8=>builder.get_undo_right(v[0].clone()),
                9=>SwitchValue(Box::new(v[0].clone()),Box::new(v[1].clone()),Box::new(v[2].clone())),
                10=>ApplyStack(Box::new(AccessStack(1)),v.into_iter().cloned().collect()),
                w=>ApplyStack(Box::new(BaseValue(builder.get_f_handle(w-11))),v.into_iter().cloned().collect()),
            };
            if a==10 {
                let biz = (0..m.len()).map(|i|{
                    let u:Vec<_> = m[i].recursion.get(&ex[0][i]).map(|x|x.iter().copied()).into_iter().flatten().collect();
                    u
                });
                let mut cart = vec![(mapping,Vec::new())];//I hate n-ary cartesian products
                for (bin,brow) in biz.enumerate() {
                    let mut buf = Vec::new();
                    if brow.len()==0 {continue 'sol;}
                    for (cmap,c) in cart {
                        'defeat: for b in brow.iter() {
                            let mut cmcl = cmap.clone();
                            match &mut cmcl {
                                None=>{
                                    let mut hm=HashMap::new();
                                    hm.insert(ex[0][bin],*b);
                                    cmcl=Some(Rc::new(hm));
                                },
                                Some(x)=> match Rc::make_mut(x).entry(ex[0][bin]) {
                                    Vacant(hole) => {hole.insert(*b);}
                                    Occupied(spot) => {
                                        if *spot.get() != *b {continue 'defeat;}
                                    }
                                }
                            }
                            let mut cl = c.clone();
                            cl.push(*b);
                            buf.push((cmcl,cl));
                        }
                    }
                    cart=buf;
                }
                for (mapping,value) in cart {
                    result.push(SolutionStatus {
                        dsl:dsl.clone(),size,value,mapping
                    })
                }
            } else {
                let value:Vec<_> = (0..m.len()).filter_map(|i|{
                    m[i].remap.get(&(a,ex.iter().map(|x|x[i]).collect())).copied()
                }).collect();
                result.push(SolutionStatus {
                    dsl,size,value,mapping
                })
            }
        }
        result
    }
}



pub type NTFA = usize;
pub struct ValueMapper {
    recursion:HashMap<usize,HashSet<usize>>,
    remap:HashMap<(usize,Vec<usize>),usize>
}
impl ValueMapper {
    fn new()->Self {
        ValueMapper {
            recursion:HashMap::new(),
            remap:HashMap::new()
        }
    }
}
pub struct PartialNTFA {
    rules:HashMap<usize,Vec<(usize,Vec<usize>)>>,
    vm:ValueMapper
}
impl PartialNTFA {
    pub fn new()->Self {PartialNTFA{rules:HashMap::new(),vm:ValueMapper::new()}}
    pub fn add_rule(&mut self,f:usize,a:Vec<usize>,r:usize) {
        if f==10 {
            self.vm.recursion.entry(a[0]).or_default().insert(r);
        } else {
            self.vm.remap.insert((f,a.clone()),r);
        }
        self.rules.entry(r).or_default().push((f,a));
    }
    pub fn convert(self,builder:&mut NTFABuilder,accstates:&HashSet<usize>)->Option<(usize,ValueMapper)> {
        struct ArtificialStack<'a> {
            outercollect: Vec<(usize,Vec<usize>)>,
            innercollect: Vec<usize>,
            outertrav:&'a [(usize,Vec<usize>)],
            innertrav:&'a [usize],
            innertoken: usize,
            place:usize
        }
        let mut stack:Vec<ArtificialStack> = Vec::new();
        let mut accepting:Vec<usize> = Vec::new();
        let mut memo:HashMap<usize,usize> = HashMap::new();
        for acc in accstates {
            if let Some(y) = self.rules.get(acc) {
                let place = builder.get_placeholder();
                memo.insert(*acc,place);
                stack.push(ArtificialStack{
                    outercollect:Vec::new(),
                    innercollect:Vec::new(),
                    outertrav:&y[1..],
                    innertrav:&y[0].1,
                    innertoken:y[0].0,
                    place
                });
                accepting.push(place);
            } else {continue;}
            while let Some(x) = stack.last_mut() {
                loop {
                    if x.innertrav.len()>0 {
                        if let Some(y) = memo.get(&x.innertrav[0]) {
                            x.innercollect.push(*y);
                            x.innertrav=&x.innertrav[1..];
                            continue;
                        } else {
                            if let Some(y) = self.rules.get(&x.innertrav[0]) {
                                let place = builder.get_placeholder();
                                memo.insert(x.innertrav[0],place);
                                stack.push(ArtificialStack{
                                    outercollect:Vec::new(),
                                    innercollect:Vec::new(),
                                    outertrav:&y[1..],
                                    innertrav:&y[0].1,
                                    innertoken:y[0].0,
                                    place
                                });
                                break;
                            } else {
                                x.innercollect.clear();
                            }
                        }
                    } else {
                        let v = take(&mut x.innercollect);
                        x.outercollect.push((x.innertoken,v));
                    }
                    if x.outertrav.len()>0 {
                        x.innertoken=x.outertrav[0].0;
                        x.innertrav=&x.outertrav[0].1;
                        x.outertrav=&x.outertrav[1..];
                    } else {
                        let ff = stack.pop().unwrap();
                        builder.insert_into_placeholder(ff.outercollect,ff.place);
                        break;
                    }
                }
            }
        }
        match builder.union(accepting) {
            Some(x) => {
                Some((x,self.vm))
            }
            None=>None
        }
    }
}



