

use std::collections::HashMap;
use std::collections::HashSet;
// use std::collections::VecDeque;
use std::collections::BinaryHeap;
use std::collections::hash_map::Entry::*;
use std::rc::Rc;
use std::mem::{take,replace,swap};
use std::iter::{*};

use crate::dsl::{*};
use crate::nftabuilder::{*};
// use crate::debug::{*};
// use crate::queue::{*};
use std::cmp::{min,max};
use std::vec::IntoIter;
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
fn dedup_merge<T:Ord>(a:Vec<T>,b:Vec<T>) -> Vec<T> {
    let mut c = Vec::with_capacity(a.len()+b.len());
    let mut a=a.into_iter();
    let mut b=b.into_iter();
    let mut xx=(a.next(),b.next());
    loop {
        match xx {
            (None,None)=>{return c;}
            (Some(x),None)=>{c.push(x);c.extend(a);return c}
            (None,Some(y))=>{c.push(y);c.extend(b);return c}
            (Some(x),Some(y))=>{
                if x<y {c.push(x);xx=(a.next(),Some(y));} else
                if y<x {c.push(y);xx=(Some(x),b.next());} else
                {c.push(x);xx=(a.next(),b.next());}
            }
        }
    }
}

pub struct NTFABuilder {
    pub paths:Vec<Vec<(usize,Vec<usize>)>>,//inner vec must be sorted
    revhash:HashMap<Vec<(usize,Vec<usize>)>,usize>,
    intersect_memo:HashMap<(usize,usize),(Option<usize>,Option<usize>,Option<usize>)>,//left side of key is less than right side
    rename_memo:HashMap<(usize,Vec<usize>),usize>,
    subset_memo:HashMap<(usize,usize),bool>,
    minification_queue:Vec<usize>,
}

impl NTFABuilder {
    pub fn new()->Self {
        NTFABuilder {
            paths:Vec::new(),//inner vec must be sorted
            revhash:HashMap::new(),
            intersect_memo:HashMap::new(),
            rename_memo:HashMap::new(),
            subset_memo:HashMap::new(),
            minification_queue:Vec::new(),
        }
    }
    fn intersect(&mut self,mut a_start:usize,mut b_start:usize)->(usize,usize,usize) {
        if b_start<a_start {swap(&mut a_start,&mut b_start)}
        struct OuterStack {
            a_start:usize,b_start:usize,
            ai:usize,bi:usize,
            totalaa:Vec<(usize,Vec<usize>)>,
            totalbb:Vec<(usize,Vec<usize>)>,
            innerstack:Vec<InnerStack>
        }
        struct InnerStack {
            amt:usize,
            alim:usize,
            blim:usize,
            x:usize,
            y:usize,
            abase:usize,
            bbase:usize,
            yi:usize,
            totalab:Vec<Vec<usize>>,
            bp : Vec<Option<usize>>,
            ap : usize,
            yab : Option<Vec<usize>>
        }
        let mut outerstack:Vec<OuterStack>=Vec::new();

        let mut ai=0;let mut bi=0;
        let mut totalaa = Vec::new();
        let mut totalbb = Vec::new();

        let mut innerstack:Vec<InnerStack>=Vec::new();

        'outerloop: loop {
            let al = &self.paths[a_start];
            let bl = &self.paths[b_start];
            'innerloop: while let Some(InnerStack{amt,alim,blim,x,y,abase,bbase,yi,totalab,bp,ap,yab}) = innerstack.last_mut() {
                let abase=*abase;let bbase=*bbase;let amt=*amt;let alim=*alim;let blim=*blim;
                let fl=al[abase].1.len();
                loop {
                    if let Some(bps) = if *x==abase {Some(&bl[bbase+*y].1[amt])} else {bp[*yi].as_ref()} {
                        let mut rw=if amt+1<fl {
                            if let Some(y)=yab {y.clone()} else {
                                let x=*x;let y=*y;let yi=*yi;
                                innerstack.push(InnerStack {
                                    yab:None,
                                    bp:Vec::new(),
                                    ap:al[x].1[amt+1].clone(),
                                    totalab:Vec::new(),
                                    x:x,y:y,yi:yi,abase:x,bbase:x,amt:amt+1,
                                    alim:al[abase+x..].iter().take(alim-abase).position(|(_,v)|v[amt] != al[abase+x].1[amt]).unwrap_or(alim),
                                    blim:bl[bbase+y..].iter().take(blim-bbase).position(|(_,v)|v[amt] != bl[bbase+y].1[amt]).unwrap_or(blim)
                                });
                                continue 'innerloop;
                            }
                        } else {Vec::new()};
                        // let mut rw = if let Some(z)=rw {z} else {continue 'innerloop;};
                        let (xaa,xab,xbb) : (Option<usize>,Option<usize>,Option<usize>) = {
                            if *ap==*bps {(None,Some(*ap),None)}
                            else {
                                match self.intersect_memo.entry((min(*ap,*bps),max(*ap,*bps))) {
                                    Occupied(z)=>{*z.get()}
                                    Vacant(z)=>{
                                        
                                        outerstack.push(OuterStack{
                                            a_start,b_start,
                                            ai,bi,
                                            totalaa:take(&mut totalaa),totalbb:take(&mut totalbb),
                                            innerstack:take(&mut innerstack)
                                        });
                                        continue 'outerloop;
                                    }
                                }
                            }
                        };

                        if let Some(z) = xab {rw.insert(0,z);totalab.push(rw);}
                        if *x==abase {bp.push(xbb);} else {bp[*yi]=xbb;}
                        *ap=match xaa {Some(z)=>z,None=>{
                            let ox=&al[abase+*x].1[amt];*x+=1;
                            while *x<alim && al[abase+*x].1[amt]!=*ox {*x+=1;}
                            if *x>=alim {break;}
                            *ap=al[abase+*x].1[amt].clone();
                            *y=0;*yi=0;
                            continue;
                        }};
                    }
                    let oy=&bl[bbase+*y].1[amt];*y+=1;
                    while *y<blim && bl[bbase+*y].1[amt]!=*oy {*y+=1;}
                    *yi+=1;
                    if *y>=blim {
                        let ox=&al[abase+*x].1[amt];totalaa.push({let mut h=al[abase+*x].clone();h.1[amt]=ap.clone();h});*x+=1;
                        while *x<alim && al[abase+*x].1[amt]!=*ox {totalaa.push({let mut h=al[abase+*x].clone();h.1[amt]=ap.clone();h});*x+=1;}
                        if *x>=alim {break;}
                        *ap=al[abase+*x].1[amt].clone();
                        *y=bbase;*yi=0;
                    }
                }
                let mut y = bbase;
                let mut yi = 0;
                while y<blim {
                    let oy=&bl[bbase+y].1[amt];
                    if let Some(z)=&bp[yi] {totalbb.push({let mut h=bl[bbase+y].clone();h.1[amt]=z.clone();h});}
                    y+=1;
                    while y<blim && bl[bbase+y].1[amt]!=*oy {
                        if let Some(z)=&bp[yi] {totalbb.push({let mut h=bl[bbase+y].clone();h.1[amt]=z.clone();h});}
                        y+=1;
                    }
                    yi+=1
                }
                
                println!("finishing a thing!");
                innerstack.pop();
            }
            // let mut int_anb=Vec::new();
            // let mut int_ab=Vec::new();
            while ai<al.len() && bi<bl.len() {
                if al[ai].0<bl[bi].0 {totalaa.push(al[ai].clone());ai+=1;}
                else if al[ai].0>bl[bi].0 {totalbb.push(bl[bi].clone());bi+=1;}
                else {
                    let f=al[ai].0;
                    let alim=al[ai..].iter().position(|(f2,_)|*f2 != f).unwrap_or(al.len()-ai);
                    let blim=bl[bi..].iter().position(|(f2,_)|*f2 != f).unwrap_or(bl.len()-bi);
                    innerstack.push(InnerStack{
                        amt:0,alim,blim,
                        x:ai,
                        y:bi,
                        abase:ai,
                        bbase:bi,
                        yi:0,
                        totalab:Vec::new(),
                        bp:Vec::new(),
                        ap:al[ai].1[0].clone(),
                        yab:None,
                    });
                    continue 'outerloop;

                    println!("make sure to simplify out some of these clones if alim,blim are singular. Simplify everytihing if alim,blim are singular.");
                    
                    ai+=alim;
                    bi+=blim;
                }
            }
            println!("do mergey simplify of everything");
            if let Some(o) = outerstack.pop() {
                a_start=o.a_start;b_start=o.b_start;
                ai=o.ai;bi=o.bi;
                totalaa=o.totalaa;
                totalbb=o.totalbb;
                innerstack=o.innerstack;
            } else {
                panic!()
            }
        }
    }

    fn indepth_simplify(&mut self,start:usize) {
        // if !self.closed_expr.insert(start) {return;}
        let mut deps = self.paths[start].clone();
        let mut a=0;
        while a<deps.len()-1 {
            let f = deps[a].0;
            let mut b=1;
            while deps[a+b].0==f {
                for c in 0..b {
                    let al = &deps[a+c].1;
                    let bl = &deps[a+b].1;
                    let mut i=0;
                    while i<al.len() && al[i] == bl[i] {i+=1;}
                    if i>=al.len() {
                        panic!("it wasn't deduped!");
                        // deps.remove(a+b);
                        // b-=1;break;
                    }
                    let l=i;
                    i+=1;
                    while i<al.len() && al[i] == bl[i] {i+=1;}
                    if i>=al.len() {
                        let mut combo : Vec<_> = dedup_merge(self.paths[al[l]].clone(),self.paths[bl[l]].clone());
                        let mut rstack = Vec::new();
                        let mut d = b+1;
                        while a+d<deps.len() && deps[a+d].0==f {
                            if (0..deps[a+c].1.len()).all(|i|i==l || deps[a+d].1[i]==deps[a+c].1[i]) {
                                combo = dedup_merge(combo,self.paths[deps[a+d].1[l]].clone());
                                rstack.push(d);
                            }
                            d+=1;
                        }
                        // println!("stack: {} {:?}",b,rstack);
                        for r in rstack.into_iter().rev() {deps.remove(a+r);}
                        deps.remove(a+b);
                        let tmp = self.get_ntfa_unchecked(combo);
                        deps[a+c].1[l]=tmp;
                        b=0;break;
                    }
                }
                b+=1;
                if a+b>=deps.len() {break;}
            }
            a+=b;
        }
        self.revhash.insert(deps.clone(),start);
        self.paths[start] = deps;
    }
    fn small_simplification(deps: &mut Vec<(usize,Vec<usize>)>) {
        deps.sort_unstable();
        deps.dedup();
    }
    fn check_requires_further(deps: &[(usize,Vec<usize>)])->bool {
        let mut requires_further = false;
        let mut a=0;
        'outer: while a<deps.len()-1 {
            let f = deps[a].0;
            let mut b=1;
            while deps[a+b].0==f {
                for c in 0..b {
                    let al = &deps[a+c].1;
                    let bl = &deps[a+b].1;
                    let mut i=0;
                    while i<al.len() && al[i] == bl[i] {i+=1;}
                    if i>=al.len() {panic!("wasn't deduped...")}
                    i+=1;
                    while i<al.len() && al[i] == bl[i] {i+=1;}
                    if i>=al.len() {
                        // println!("rewuires: {}   {:?} {:?}",f,al,bl);
                        requires_further=true;
                        break 'outer;
                    }
                }
                b+=1;
                if a+b>=deps.len() {break;}
            }
            a+=b;
        } requires_further
    }
    
    fn get_ntfa(&mut self,mut deps:Vec<(usize,Vec<usize>)>)->usize {
        NTFABuilder::small_simplification(&mut deps);
        self.get_ntfa_unchecked(deps)
    }
    fn get_ntfa_unchecked(&mut self,deps:Vec<(usize,Vec<usize>)>)->usize {
        match self.revhash.entry(deps) {
            Occupied(x)=>*x.get(),
            Vacant(x)=>{
                let i=self.paths.len();
                if NTFABuilder::check_requires_further(x.key()) {
                    self.minification_queue.push(i);
                }
                self.paths.push(x.key().clone());
                x.insert(i); i
            }
        }
    }

    fn get_placeholder(&mut self)->usize {
        self.paths.push(vec![]);
        self.paths.len()-1
    }

    fn insert_into_placeholder(&mut self,mut deps:Vec<(usize,Vec<usize>)>,i:usize)->usize {
        NTFABuilder::small_simplification(&mut deps);
        match self.revhash.entry(deps) {
            Occupied(x)=>*x.get(),//release i back to the cluster...
            Vacant(x)=>{
                if NTFABuilder::check_requires_further(x.key()) {
                    self.minification_queue.push(i);
                }
                self.paths[i]=x.key().clone();
                x.insert(i); i
            }
        }
    }

    pub fn forget_minification_queue(&mut self) {
        self.minification_queue = Vec::new();
    }

    pub fn deplete_minification_queue(&mut self) {
        while let Some(i) = self.minification_queue.pop() {
            self.indepth_simplify(i);
        }
    }

    // pub fn getmergedvl(&self,ind:Vec<(usize,usize)>)->IntoIter<(usize,Vec<Vec<(usize,usize)>>)> {
    //     let mut buf_a:Vec<(usize,Vec<usize>)>;let mut buf_b:Vec<(usize,Vec<usize>)>;
    //     let (al,bl) : (&[(usize,Vec<usize>)],&[(usize,Vec<usize>)]) = if ind.len()>1 {
    //         buf_a = Vec::new();
    //         buf_b = Vec::new();
    //         for (sa,sb) in ind {
    //             buf_a.extend(self.paths[sa].clone());
    //             buf_b.extend(self.paths[sb].clone());
    //         }
    //         buf_a.sort_unstable();
    //         buf_b.sort_unstable();
    //         buf_a.dedup();
    //         buf_b.dedup();
    //         (&buf_a,&buf_b)
    //     } else {
    //         (&self.paths[ind[0].0],&self.paths[ind[0].1])
    //     };
    //     let mut a=0;
    //     let mut b=0;
    //     let mut ao;
    //     let mut bo;
    //     let mut deps = Vec::new();
    //     while a<al.len() && b<bl.len() {
    //         if al[a].0<bl[b].0 {a+=1;}
    //         else if al[a].0>bl[b].0 {b+=1;}
    //         else {
    //             let f=al[a].0;
    //             ao=0;
    //             bo=0;
    //             while a+ao<al.len() && al[a+ao].0==f {
    //                 bo=0;
    //                 while b+bo<bl.len() && bl[b+bo].0==f {
    //                     let mut res = Vec::new();
    //                     for i in 0..al[a+ao].1.len() {
    //                         res.push(vec![(min(al[a+ao].1[i],bl[b+bo].1[i]),max(al[a+ao].1[i],bl[b+bo].1[i]))]);
    //                     }
    //                     deps.push((f,res));
    //                     bo+=1;
    //                 }
    //                 ao+=1;
    //             }
    //             a+=ao;
    //             b+=bo;
    //         }
    //     }
    //     deps.sort_unstable();
    //     let mut a=0;
    //     while a+1<deps.len() {
    //         // println!("checkpoint 1: {} {}",deps.len(),a);
    //         let f = deps[a].0;
    //         let mut b=1;
    //         while deps[a+b].0==f {
    //             for c in 0..b {
    //                 let al = &deps[a+c].1;
    //                 let bl = &deps[a+b].1;
    //                 let mut i=0;
    //                 while i<al.len() && al[i] == bl[i] {i+=1;}
    //                 if i>=al.len() {
    //                     deps.remove(a+b);
    //                     b-=1;break;
    //                 }
    //                 let l=i;
    //                 i+=1;
    //                 while i<al.len() && al[i] == bl[i] {i+=1;}
    //                 if i>=al.len() {
    //                     let depr = take(&mut deps.remove(a+b).1[l]);
    //                     deps[a+c].1[l] = dedup_merge(take(&mut deps[a+c].1[l]),depr);
    //                     b=0;break;
    //                 }
    //             }
    //             b+=1;
    //             if a+b>=deps.len() {break;}
    //         }
    //         a+=b;
    //     } deps.into_iter()
    // }

    // pub fn intersect(&mut self,a_start:usize,b_start:usize) -> Option<usize> {
    //     if a_start==b_start {return Some(a_start);}
    //     struct ArtificialStack {
    //         outercollect: Vec<(usize,Vec<usize>)>,
    //         innercollect: Vec<usize>,
    //         outertrav: IntoIter<(usize,Vec<Vec<(usize,usize)>>)>,
    //         innertrav: Vec<Vec<(usize,usize)>>,
    //         innertoken: usize,
    //         place:usize
    //     }
    //     let mut stack:Vec<ArtificialStack> = Vec::new();
    //     let snok = vec![(min(a_start,b_start),max(a_start,b_start))];
    //     let place = self.get_placeholder();
    //     self.intersect_memo.insert(snok.clone(),Some(place));
    //     let mut outertrav = self.getmergedvl(snok);
    //     let (innertoken,intv) = match outertrav.next() {
    //         Some(x)=>x,None=>{return None;}
    //     };
    //     stack.push(ArtificialStack{
    //         outercollect:Vec::new(),
    //         innercollect:Vec::new(),
    //         outertrav,
    //         innertoken,
    //         innertrav:intv,
    //         place,
    //     });
    //     loop {
    //         let x = stack.last_mut().unwrap();
    //         loop {
    //             if let Some(subl) = x.innertrav.pop() {
    //                 match if subl.len()==1 && (subl[0].0==subl[0].1 || Some(subl[0].1)==self.uneval_hack) {Some(Some(subl[0].0))}
    //                     else if subl.len()==1 && Some(subl[0].0)==self.uneval_hack {Some(Some(subl[0].1))}
    //                     else {self.intersect_memo.get(&subl).copied()} {
    //                     Some(Some(y))=>{x.innercollect.push(y);continue;}
    //                     Some(None)=>{x.innercollect.clear();}
    //                     None=>{
    //                         let mut outertrav = self.getmergedvl(subl.clone());
    //                         if let Some((innertoken,intv)) = outertrav.next() {
    //                             let place = self.get_placeholder();
    //                             self.intersect_memo.insert(subl.clone(),Some(place));
    //                             x.innertrav.push(subl);
    //                             stack.push(ArtificialStack{
    //                                 outercollect:Vec::new(),
    //                                 innercollect:Vec::new(),
    //                                 outertrav,
    //                                 innertoken,
    //                                 innertrav:intv,
    //                                 place,
    //                             });
    //                             break;
    //                         } else {x.innercollect.clear();}
    //                     }
    //                 }
    //             } else {
    //                 let v = take(&mut x.innercollect);
    //                 x.outercollect.push((x.innertoken,v));
    //             }
    //             if let Some((innertoken,intv))=x.outertrav.next() {
    //                 x.innertoken=innertoken;
    //                 x.innertrav=intv;
    //             } else {
    //                 let ff = stack.pop().unwrap();
    //                 let rpv = if ff.outercollect.len()==0 {None} else {Some(self.insert_into_placeholder(ff.outercollect,ff.place))};
    //                 match stack.last() {
    //                     Some(x)=>{
    //                         if rpv != Some(ff.place) {
    //                             let fl = x.innertrav.last().unwrap();
    //                             self.intersect_memo.insert(fl.clone(),rpv);//harmlessly replace old value
    //                         }
    //                     }
    //                     None=>{
    //                         return rpv
    //                     }
    //                 }
    //                 break;
    //             }
    //         }
    //     }
    // }

    pub fn get_accepting_run(
        &self,
        start:usize,
        builder:&mut ExpressionBuilder,
        map:&[ValueMapper]
    ) -> Vec<(Dsl,usize,HashMap<usize,usize>)> {
        let mut queue : BinaryHeap<SolutionStatusWrap> = BinaryHeap::new();
        queue.push(SolutionStatusWrap(start,0,None));
        let mut solns : HashMap<usize,Vec<Rc<SolutionStatus>>> = HashMap::new();
        let mut working : HashMap<usize,Vec<(&[usize],Vec<Rc<SolutionStatus>>,usize,usize,usize)>> = HashMap::new();
        let mut visited : HashSet<usize> = HashSet::new();
        while let Some(SolutionStatusWrap(x,minsize,updown)) = queue.pop() {
            let mut stack:Vec<(&[usize],Vec<Rc<SolutionStatus>>,usize,usize,usize)> = Vec::new();
            match updown {
                None=>{
                    if !visited.insert(x) {continue;}
                    let y = &self.paths[x];
                    if let Some((f,_)) = y.iter().find(|(_,x)|x.len()==0) {
                        for sol in SolutionStatus::transfix(*f,&vec![],map,builder) {
                            queue.push(SolutionStatusWrap(x,minsize+1,Some(sol)));
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
                    for sol in SolutionStatus::transfix(f,&v,map,builder) {
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
            (a.clone(),*b,c.as_ref().map(|x|(**x).clone()).unwrap_or_default())
        }).collect()
    }
}



#[derive(Clone,Debug)]
pub struct SolutionStatus {
    dsl:Dsl,
    size:usize,
    value:Vec<usize>,
    mapping:Option<Rc<HashMap<usize,usize>>>
}
#[derive(Debug)]
struct SolutionStatusWrap(usize,usize,Option<SolutionStatus>);
impl Eq for SolutionStatusWrap {}
impl Ord for SolutionStatusWrap {
    fn cmp(&self, other: &Self) -> Ordering {
        other.1.cmp(&self.1)
    }
}
impl PartialOrd for SolutionStatusWrap {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(other.1.cmp(&self.1))
    }
}
impl PartialEq<SolutionStatusWrap> for SolutionStatusWrap {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
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
    fn insert(self,l:&mut Vec<Rc<SolutionStatus>>) -> Option<&mut Rc<SolutionStatus>> {
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
        a:usize,
        v:&Vec<Rc<SolutionStatus>>,
        m:&[ValueMapper],
        builder:&mut ExpressionBuilder
    )->Vec<SolutionStatus> {
        let size = v.iter().map(|x|x.size).sum::<usize>()+1;
        let ex = v.iter().map(|x|&x.value).collect::<Vec<_>>();
        let mapping = match v.iter().fold(Some(None),|a,x|match (a.clone(),x.mapping.clone()) {
            (None,_)=>None,
            (Some(None),None)=>Some(None),
            (Some(Some(x)),None)|(Some(None),Some(x))=>Some(Some(x)),
            (Some(Some(mut x)),Some(mut y))=>disjoint_union(
                take(Rc::make_mut(&mut x)),
                take(Rc::make_mut(&mut y))
            ).map(|x|Some(Rc::new(x)))
        }) {Some(x)=>x,None=>{return Vec::new();}};
        let v = v.iter().map(|x|&x.dsl).collect::<Vec<_>>();
        let mut result = Vec::new();
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
                if brow.len()==0 {return Vec::new()}
                for (cmap,c) in cart {
                    'defeat: for b in brow.iter() {
                        let mut cmcl = cmap.clone();
                        if ex[0][bin]!=0 && *b!=0 {
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
        result
    }
}



pub type NTFA = usize;
#[derive(Default)]
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
#[derive(Default)]
pub struct PartialNTFA {
    pub rules:HashMap<usize,Vec<(usize,Vec<usize>)>>,
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
    pub fn getmergedvl<T:Iterator<Item=usize>>(&self,ind:T)->IntoIter<(usize,Vec<Vec<usize>>)> {
        let mut deps:Vec<(usize,Vec<Vec<usize>>)> = Vec::new();
        for s in ind {deps.extend(self.rules.get(&s).into_iter().map(|ii|ii.iter().map(|(f,a)|(*f,a.iter().map(|x|vec![*x]).collect()))).flatten());}
        deps.sort_unstable();
        let mut a=0;
        while a<deps.len()-1 {
            let f = deps[a].0;
            let mut b=1;
            while deps[a+b].0==f {
                for c in 0..b {
                    let al = &deps[a+c].1;
                    let bl = &deps[a+b].1;
                    let mut i=0;
                    while i<al.len() && al[i] == bl[i] {i+=1;}
                    if i>=al.len() {
                        deps.remove(a+b);
                        b-=1;break;
                    }
                    let l=i;
                    i+=1;
                    while i<al.len() && al[i] == bl[i] {i+=1;}
                    if i>=al.len() {
                        let depr = take(&mut deps.remove(a+b).1[l]);
                        deps[a+c].1[l] = dedup_merge(take(&mut deps[a+c].1[l]),depr);
                        b=0;break;
                    }
                }
                b+=1;
                if a+b>=deps.len() {break;}
            }
            a+=b;
        } deps.into_iter()
    }
    // pub fn convert(self,builder:&mut NTFABuilder,accstates:&HashSet<usize>)->Option<(usize,ValueMapper)> {
    //     if accstates.len()==0 {return None}
    //     struct ArtificialStack {
    //         outercollect: Vec<(usize,Vec<usize>)>,
    //         innercollect: Vec<usize>,
    //         outertrav: IntoIter<(usize,Vec<Vec<usize>>)>,
    //         innertrav: Vec<Vec<usize>>,
    //         innertoken: usize,
    //         place:usize
    //     }
    //     let mut stack:Vec<ArtificialStack> = Vec::new();
    //     let mut memo:HashMap<Vec<usize>,Option<usize>> = HashMap::new();

    //     let mut snok = accstates.iter().copied().collect::<Vec<_>>();
    //     snok.sort_unstable();
    //     let place = builder.get_placeholder();
    //     memo.insert(snok.clone(),Some(place));
    //     let mut outertrav = self.getmergedvl(accstates.iter().copied());
    //     let (innertoken,intv) = outertrav.next().unwrap();
    //     stack.push(ArtificialStack{
    //         outercollect:Vec::new(),
    //         innercollect:Vec::new(),
    //         outertrav,
    //         innertoken,
    //         innertrav:intv,
    //         place,
    //     });
    //     loop {
    //         let x = stack.last_mut().unwrap();
    //         loop {
    //             if let Some(subl) = x.innertrav.pop() {
    //                 match if subl[0]==0 {builder.uneval_hack.map(|w|Some(w))} else {memo.get(&subl).copied()} {
    //                     Some(Some(y))=>{x.innercollect.push(y);continue;}
    //                     Some(None)=>{x.innercollect.clear();}
    //                     None=>{
    //                         let mut outertrav = self.getmergedvl(subl.iter().copied());
    //                         if let Some((innertoken,intv)) = outertrav.next() {
    //                             let place = builder.get_placeholder();
    //                             if subl[0]==0 {builder.uneval_hack = Some(place);} else {memo.insert(subl.clone(),Some(place));}
    //                             x.innertrav.push(subl);
    //                             stack.push(ArtificialStack{
    //                                 outercollect:Vec::new(),
    //                                 innercollect:Vec::new(),
    //                                 outertrav,
    //                                 innertoken,
    //                                 innertrav:intv,
    //                                 place,
    //                             });
    //                             break;
    //                         } else {x.innercollect.clear();}
    //                     }
    //                 }
    //             } else {
    //                 let v = take(&mut x.innercollect);
    //                 x.outercollect.push((x.innertoken,v));
    //             }
    //             if let Some((innertoken,intv))=x.outertrav.next() {
    //                 x.innertoken=innertoken;
    //                 x.innertrav=intv;
    //             } else {
    //                 let ff = stack.pop().unwrap();
    //                 let rpv = if ff.outercollect.len()==0 {None} else {Some(builder.insert_into_placeholder(ff.outercollect,ff.place))};
    //                 match stack.last() {
    //                     Some(x)=>{
    //                         if rpv != Some(ff.place) {
    //                             let fl = x.innertrav.last().unwrap();
    //                             if fl[0]==0 {panic!("what?")}
    //                             memo.insert(fl.clone(),rpv);//harmlessly replace old value
    //                         }
    //                     }
    //                     None=>{
    //                         builder.deplete_minification_queue();
    //                         return rpv.map(|x|(x,self.vm))
    //                     }
    //                 }
    //                 break;
    //             }
    //         }
    //     }
    // }
}



