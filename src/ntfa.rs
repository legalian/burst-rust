

use std::collections::HashMap;
use std::collections::HashSet;
// use std::collections::VecDeque;
use std::collections::BinaryHeap;
use std::collections::hash_map::Entry::*;
use std::rc::Rc;
use std::mem::{take};//,swap};
use std::iter::{*};
// use std::iter::once;

use crate::dsl::{*};
use crate::nftabuilder::{*};
// use crate::debug::{*};
// use crate::queue::{*};
use std::cmp::{min,max};
use std::vec::IntoIter;
use std::cmp::Ordering;
use Ordering::{*};
use Dsl::{*};
// use ProcType::{*};
use ProcValue::{*};


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
fn dedup_intersect<T:Ord>(a:Vec<T>,b:Vec<T>) -> Vec<T> {
    let mut c = Vec::with_capacity(a.len()+b.len());
    let mut a=a.into_iter();
    let mut b=b.into_iter();
    let mut xx=(a.next(),b.next());
    loop {
        match xx {
            (None,_)|(_,None)=>{return c;}
            (Some(x),Some(y))=>{
                if x<y {xx=(a.next(),Some(y));} else
                if y<x {xx=(Some(x),b.next());} else
                {c.push(x);xx=(a.next(),b.next());}
            }
        }
    }
}
fn dedup_setminus<T:Ord>(a:Vec<T>,b:Vec<T>) -> Vec<T> {
    let mut c = Vec::with_capacity(a.len()+b.len());
    let mut a=a.into_iter();
    let mut b=b.into_iter();
    let mut xx=(a.next(),b.next());
    loop {
        match xx {
            (None,_)=>{return c;}
            (Some(x),None)=>{c.push(x);c.extend(a);return c}
            (Some(x),Some(y))=>{
                if x<y {c.push(x);xx=(a.next(),Some(y));} else
                if y<x {xx=(Some(x),b.next());} else
                {xx=(a.next(),b.next());}
            }
        }
    }
}


pub struct NTFABuilder {
    pub input_type:usize,
    pub output_type:usize,
    pub paths:Vec<Vec<(usize,Vec<usize>)>>,//inner vec must be sorted
    pub revhash:HashMap<Vec<(usize,Vec<usize>)>,usize>,
    pub intersect_memo:HashMap<(usize,usize),Option<usize>>,//left side of key is less than right side
    // pub rename_memo:HashMap<(usize,Vec<usize>),usize>,
    // pub subset_memo:HashMap<(usize,usize),bool>,
    // minification_queue:Vec<usize>,
    pub purgeset:HashSet<usize>
}


struct OccuranceTracker {
    unconfirmed:HashSet<usize>,
    occurances:HashMap<usize,HashSet<usize>>,
}
impl OccuranceTracker {
    fn new() -> Self { 
        OccuranceTracker{
            unconfirmed:HashSet::new(),
            occurances:HashMap::new()
        }
    }
    fn add_unconfirmed(&mut self,a:usize) {
        self.unconfirmed.insert(a);
        self.occurances.insert(a,HashSet::new());
    }
    fn forget(&mut self,a:usize) {
        self.unconfirmed.remove(&a);
        self.occurances.remove(&a);
    }
    fn depends_on(&mut self,a:usize,v:&Vec<(usize,Vec<usize>)>){
        for (_,w) in v {
            for u in w {
                if let Some(k) = self.occurances.get_mut(u) {
                    k.insert(a);
                }
            }
        }
    }
    fn kill_unused_and_report(mut self,mut rtrack:Option<usize>,builder:&mut NTFABuilder)->Option<usize> {
        println!("killing unused...");
        let mut stack : Vec<usize> = self.unconfirmed.iter().copied().collect();
        while let Some(a) = stack.pop() {
            if !self.unconfirmed.contains(&a) {continue;}
            if builder.paths[a].iter().any(|(_,y)|y.iter().all(|x|!self.unconfirmed.contains(x))) {
                self.unconfirmed.remove(&a);
                for j in self.occurances[&a].iter() {
                    if self.unconfirmed.contains(j) {
                        // println!("adding to stack: {:?}",*j);
                        stack.push(*j)
                    }
                }
            }
        }
        println!("checkpoint killing unused...");
        let mut rstack : Vec<usize> = self.unconfirmed.into_iter().collect();
        let mut visited = HashSet::new();
        while let Some(a) = rstack.pop() {
            if !visited.insert(a) {continue;}
            println!("killing: {}",a);
            // if b.is_none() {println!("killing: {}",a)}
            if rtrack==Some(a) {rtrack=None;}
            for occurance in self.occurances[&a].iter().copied() {
                let v = &mut builder.paths[occurance];
                // builder.revhash.remove(v);
                // match b {
                //     Some(b) => {
                //         for (_,w) in v.iter_mut() {
                //             for u in w.iter_mut() {
                //                 if *u==a {*u=b;}
                //             }
                //         }
                //     }
                    // None => {
                for i in (0..v.len()).rev() {
                    if v[i].1.iter().any(|u|*u==a) {v.remove(i);}
                }
                    // }
                // }
                if v.len()==0 {
                    rstack.push(occurance);
                }
                // else {
                //     match builder.revhash.entry(v.clone()) {
                //         Vacant(x)=>{x.insert(occurance);}
                //         Occupied(x)=>{rstack.push((occurance,Some(*x.get())));}
                //     }
                // }
            }
        }
        println!("finished killing unused...");
        rtrack
    }
}




impl NTFABuilder {
    pub fn purge(&mut self,h:usize) {
        let mut stack : Vec<usize> = vec![h];
        while let Some(z) = stack.pop() {
            if self.paths[z].len()==0 {panic!("purge failed!");}
            for (_,a) in self.paths[z].iter() {
                for c in a.iter().copied() {
                    if self.purgeset.insert(c) {
                        stack.push(c);
                    }
                }
            }
        }
    }
    pub fn intersect(&mut self,a_start:usize,b_start:usize)->Option<usize> {
        if a_start==b_start {return Some(a_start);}
        if a_start==0 {return Some(a_start);}
        if 0==b_start {return Some(b_start);}
        struct ArtificialStack {
            outercollect: Vec<(usize,Vec<usize>)>,
            innercollect: Vec<usize>,
            outertrav: IntoIter<(usize,Vec<(usize,usize)>)>,
            innertrav: Vec<(usize,usize)>,
            innertoken: usize,
            place:usize
        }
        let mut stack:Vec<ArtificialStack> = Vec::new();
        let outerkey = (min(a_start,b_start),max(a_start,b_start));
        let place = match self.intersect_memo.entry(outerkey) {
            Vacant(_) => {
                let place = self.get_placeholder();
                self.intersect_memo.insert(outerkey,Some(place));place
            }
            Occupied(z)=>{return *z.get();}
        };

        fn getmergedvl(al:&[(usize,Vec<usize>)],bl:&[(usize,Vec<usize>)])->IntoIter<(usize,Vec<(usize,usize)>)> {
            let mut a=0;
            let mut b=0;
            let mut ao;
            let mut bo;
            let mut deps = Vec::new();
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
                            for i in 0..al[a+ao].1.len() {
                                res.push((min(al[a+ao].1[i],bl[b+bo].1[i]),max(al[a+ao].1[i],bl[b+bo].1[i])));
                            }
                            deps.push((f,res));
                            bo+=1;
                        }
                        ao+=1;
                    }
                    a+=ao;
                    b+=bo;
                }
            }
            for (_,j) in deps.iter_mut() {j.reverse();}
            deps.into_iter()
        }

        let mut outertrav = getmergedvl(&self.paths[a_start],&self.paths[b_start]);
        let (innertoken,intv) = match outertrav.next() {
            Some(x)=>x,None=>{return None;}
        };
        // let mut tracker = OccuranceTracker::new();
        // tracker.add_unconfirmed(place);
        stack.push(ArtificialStack{
            outercollect:Vec::new(),
            innercollect:Vec::new(),
            outertrav,
            innertoken,
            innertrav:intv,
            place,
        });
        loop {
            let x = stack.last_mut().unwrap();
            loop {
                if let Some(subl) = x.innertrav.pop() {
                    match if subl.0==0 || subl.0==subl.1 {Some(Some(subl.1))}
                        else {self.intersect_memo.get(&subl).copied()} {
                        Some(Some(y))=>{x.innercollect.push(y);continue;}
                        Some(None)=>{x.innercollect.clear();}
                        None=>{
                            let mut outertrav = getmergedvl(&self.paths[subl.0],&self.paths[subl.1]);
                            if let Some((innertoken,intv)) = outertrav.next() {
                                let place = self.get_placeholder();
                                self.intersect_memo.insert(subl.clone(),Some(place));
                                x.innertrav.push(subl);
                                // tracker.add_unconfirmed(place);
                                stack.push(ArtificialStack{
                                    outercollect:Vec::new(),
                                    innercollect:Vec::new(),
                                    outertrav,
                                    innertoken,
                                    innertrav:intv,
                                    place,
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
                    // tracker.depends_on(ff.place,&ff.outercollect);
                    let rpv = if ff.outercollect.len()==0 {None} else {Some(self.insert_into_placeholder(ff.outercollect,ff.place))};
                    match stack.last() {
                        Some(x)=>{
                            if rpv != Some(ff.place) {
                                panic!("forgetting! returning none!");
                                // tracker.forget(ff.place);
                                let fl = *x.innertrav.last().unwrap();
                                self.intersect_memo.insert(fl,rpv);//harmlessly replace old value
                            }
                        }
                        None=>{
                            if rpv != Some(ff.place) {
                                // tracker.forget(ff.place);
                                // let fl = x.innertrav.last().unwrap();
                                self.intersect_memo.insert(outerkey,rpv);//harmlessly replace old value
                            }
                            // let rpv = tracker.kill_unused_and_report(rpv,self);
                            return rpv
                        }
                    }
                    break;
                }
            }
        }
    }

    fn get_ntfa(&mut self,deps:Vec<(usize,Vec<usize>)>)->usize {
        if deps.len()==0 {panic!()}
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
        let i=self.paths.len();
        self.paths.push(deps); i
    }

    fn get_placeholder(&mut self)->usize {
        self.paths.push(Vec::new());
        self.paths.len()-1
    }

    fn insert_into_placeholder(&mut self,mut deps:Vec<(usize,Vec<usize>)>,i:usize)->usize {
        if deps.len()==0 {panic!()}
        deps.sort_unstable();
        deps.dedup();
        // match self.revhash.entry(deps) {
        //     Occupied(x)=>*x.get(),//release i back to the cluster...
        //     Vacant(x)=>{
        //         // if NTFABuilder::check_requires_further(x.key()) {
        //         //     self.minification_queue.push(i);
        //         // }
        //         self.paths[i]=x.key().clone();
        //         x.insert(i); i
        //     }
        // }
        self.paths[i]=deps; i
    }

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
                        // println!("found nullary!");
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


    pub fn simplify(&mut self,accstates:Vec<usize>)->Option<usize> {

        // self.purge(a_start);
        // if accstates.len()==0 {return None}
        // if accstates.len()==1 {return Some(accstates[0])}
        // panic!();
        // let mut deps:Vec<(usize,Vec<usize>)> = Vec::new();
        // for s in accstates {deps.extend(self.paths[s].iter().cloned())}
        // return Some(self.get_ntfa(deps));

        if accstates.len()==0 {return None}
        let mut ownership : HashMap<usize,usize> = accstates.iter().map(|x|(*x,0)).collect();
        let mut stack : Vec<usize> = accstates.clone();
        let mut nonaccstates : Vec<usize> = Vec::new();
        let mut invocc : HashMap<usize,Vec<((usize,&[usize],&[usize]),usize)>> = HashMap::new();
        while let Some(z) = stack.pop() {
            for (f,a) in self.paths[z].iter() {
                for (i,c) in a.iter().copied().enumerate() {
                    invocc.entry(c).or_default().push(((*f,&a[..i],&a[i+1..]),z));
                    match ownership.entry(c) {
                        Occupied(_)=>{},
                        Vacant(v)=>{
                            v.insert(1);
                            stack.push(c);
                            nonaccstates.push(c);
                        }
                    }
                }
            }
        }
        let mut hotpools : HashSet<usize> = HashSet::new();
        hotpools.insert(0);
        let mut pools : Vec<(Vec<usize>,Vec<usize>)> = if nonaccstates.len()==0 {
            vec![(accstates.clone(),Vec::new())]
        } else {
            hotpools.insert(1);
            vec![(accstates.clone(),Vec::new()),(nonaccstates,accstates.clone())]
        };



        let mut eyes : HashMap<usize,HashSet<usize>> = HashMap::new();
        let mut hotmemo : HashMap<usize,Vec<(&(usize,&[usize],&[usize]),usize)>> = HashMap::new();
        while hotpools.len()>0 {
            let i = *hotpools.iter().next().unwrap();
            if pools[i].0.len()==1 && pools[i].1.len()==0 {
                hotpools.remove(&i);
                continue;
            }
            fn getblh<'a,'b>(
                invocc:&'a HashMap<usize,Vec<((usize,&'a [usize],&'a [usize]),usize)>>,
                ownership:&'b HashMap<usize,usize>,
                g:usize
            )->Vec<(&'a (usize,&'a [usize],&'a [usize]),usize)> {
                let mut blh : Vec<(&(usize,&[usize],&[usize]),usize)> = Vec::new();
                for (key,r) in invocc.get(&g).map(|g|g.iter()).into_iter().flatten() {
                    blh.push((key,ownership[r]));
                }
                blh.sort_unstable();
                blh.dedup();
                blh
            }
            fn is_superset(
                a:&[(&(usize,&[usize],&[usize]),usize)],
                b:&[(&(usize,&[usize],&[usize]),usize)]
            )->bool {
                if a.len()<b.len() {return false}
                let mut ia=0;let mut ib=0;
                while ia<a.len() && ib<b.len() {
                    match a[ia].cmp(&b[ib]) {
                        Less=>{ia+=1;}
                        Greater=>{return false}
                        Equal=>{ia+=1;ib+=1;}
                    }
                } !(ia==a.len() && ib<b.len())
            }
            let mut differentiator : HashMap<&[(&(usize,&[usize],&[usize]),usize)],Vec<usize>> = HashMap::new();
            for ow in pools[i].0.iter() {
                match hotmemo.entry(*ow) { Vacant(z)=>{z.insert(getblh(&invocc,&ownership,*ow));} _=>{} }
            }
            for sub in pools[i].1.iter() {
                match hotmemo.entry(*sub) { Vacant(z)=>{z.insert(getblh(&invocc,&ownership,*sub));} _=>{} }
            }
            for ow in pools[i].0.iter() {
                differentiator.entry(&hotmemo[ow]).or_default().push(*ow);
            }

            let mut result : Vec<_> = differentiator.into_iter().map(|(a,b)|(a,b,Vec::new())).collect();
            for x in 0..result.len()-1 {
                for y in x+1..result.len() {
                    let (fst,lst) = result[x..].split_first_mut().unwrap();
                    if is_superset(fst.0,lst[y-x-1].0) {
                        lst[y-x-1].2.extend(fst.1.iter().copied());
                    }
                    if is_superset(lst[y-x-1].0,fst.0) {
                        fst.2.extend(lst[y-x-1].1.iter().copied());
                    }
                }
            }
            for sub in pools[i].1.iter() {
                let ghl = &hotmemo[sub];
                for (t,_,r) in result.iter_mut() {
                    if is_superset(ghl,t) {r.push(*sub);}
                }
            }
            
            if result.len()>1 {
                let mut result = result.into_iter();
                let ff = result.next().unwrap();
                pools[i].0 = ff.1;
                pools[i].1 = ff.2;
                for (_,v,w) in result {
                    for k in v.iter() {
                        ownership.insert(*k,pools.len());
                    }
                    hotpools.insert(pools.len());
                    pools.push((v,w));
                }
                if let Some(z) = eyes.remove(&i) {
                    for j in z {
                        hotpools.insert(j);
                    }
                }
                hotmemo.retain(|_,v|!v.iter().any(|(_,y)|*y==i));
            } else {
                let wk = result.remove(0);
                for w in wk.0 {
                    eyes.entry(w.1).or_default().insert(i);
                }
                pools[i].1 = wk.2;
                hotpools.remove(&i);
            }
        }

        println!("\n\n{:?}\n{:?}\n\n",pools,ownership);
        // 'stupid: loop{{{
        //         let mut stack : Vec<usize> = accstates.clone();
        //         let mut dedup : HashSet<usize> = HashSet::new();
        //         while let Some(z) = stack.pop() {
        //             println!("{:?} := {:?}",z,self.paths[z]);
        //             for (_,a) in self.paths[z].iter() {
        //                 for c in a.iter().copied() {
        //                     if dedup.insert(c) {
        //                         stack.push(c);
        //                     }
        //                 }
        //             }
        //         }
        //         break
        // }}}

        let mut hs = HashSet::new();
        let mut oup = Vec::new();
        for b in accstates {
            if hs.insert(b) {
                let own = ownership[&b];
                oup.push(own);
                hs.extend(pools[own].0.iter().copied());
                hs.extend(pools[own].1.iter().copied());
            }
        }
        if pools.iter().all(|(a,b)|a.len()==1&&b.len()==0) {
            if oup.len()==1 {return Some(pools[oup[0]].0[0])}
            let mut deps:Vec<(usize,Vec<usize>)> = Vec::new();
            for s in oup {deps.extend(self.paths[pools[s].0[0]].iter().cloned())}
            return Some(self.get_ntfa(deps));
        }

        fn getmergedvl(
            sel:&NTFABuilder,
            item:usize,
            pools:&Vec<(Vec<usize>,Vec<usize>)>,
            ownership:&HashMap<usize,usize>
        )->IntoIter<(usize,Vec<usize>)> {
            let mut deps:Vec<(usize,Vec<usize>)> = Vec::new();
            for s in pools[item].0.iter().copied() {deps.extend(sel.paths[s].iter().cloned())}
            for s in pools[item].1.iter().copied() {deps.extend(sel.paths[s].iter().cloned())}
            deps.sort_unstable();
            deps.dedup();
            // println!("deps len: {:?} {:?} {:?}",deps.len(),pools[item].0.len(),pools[item].1.len());
            let mut a=0;
            // let OLDDEPS = deps.clone();
            while a<deps.len() {
                let f = deps[a].0;
                let l = deps[a].1.len();
                let mut b=1;
                while a+b<deps.len() && deps[a+b].0==f {
                    b+=1;
                }
                // if f==9 {println!("deps before after: {:?} {:?} {:?}",deps,a,b)}
                for amt in 0..l {
                    let mut x=0;
                    let mut partition=b;
                    while x<partition {
                        let mut y = x;
                        let mut collect:Vec<usize> = Vec::new();
                        let mut hs = HashSet::new();
                        // let mut DEBUG_HS2 = HashSet::new();
                        while y<partition {
                            if (0..l).all(|a2|a2==amt || deps[a+x].1[a2]==deps[a+y].1[a2]) {
                                let ncent = deps[a+y].1[amt];
                                // println!("{:?} (owner:{:?})",ncent,ownership[&ncent]);
                                // DEBUG_HS2.insert(ncent);
                                if hs.insert(ncent) {
                                    let own = ownership[&ncent];
                                    collect.push(own);
                                    // println!("extending {:?} {:?}",own,pools[own]);
                                    hs.extend(pools[own].0.iter().copied());
                                    if pools[own].1.len()>0 {
                                        collect.retain(|x|!pools[own].1.contains(x));
                                    }
                                    hs.extend(pools[own].1.iter().copied());
                                }
                                if y!=x {
                                    deps.remove(a+y);
                                    // if f==9 {println!("5 removal??! {:?}",RMRMRM);}
                                    b-=1;
                                    partition-=1;
                                } else {y+=1}
                            } else {y+=1;}
                        }
                        // for HHH in hs.iter() {
                        //     if !DEBUG_HS2.contains(&HHH) {
                        //         panic!("OH NO {:?} {:?}",HHH,DEBUG_HS2);
                        //     }
                        // }
                        // println!("=>{:?} {:?}",hs,collect);
                        deps[a+x].1[amt]=collect.pop().unwrap();
                        for col in collect {
                            let mut cr = deps[a+x].clone();
                            cr.1[amt] = col;
                            deps.insert(a+partition,cr);
                            b+=1;
                        }
                        x+=1;
                    }

                }
                // if f==9 {println!("deps snapshot after: {:?} {:?} {:?}",deps,a,b)}
                a+=b;
            }
            // println!("transform: {:?} => {:?}",OLDDEPS,deps);
            deps.sort_unstable();
            for (_,v) in deps.iter_mut() {
                v.reverse();
            }
            deps.into_iter()
        }
        struct ArtificialStack {
            outercollect: Vec<(usize,Vec<usize>)>,
            innercollect: Vec<usize>,
            outertrav: IntoIter<(usize,Vec<usize>)>,
            innertrav: Vec<usize>,
            innertoken: usize,
            place: usize,
        }
        let mut memo:HashMap<usize,usize> = HashMap::new();
        let mut result = Vec::new();
        for own in oup {
            let mut stack:Vec<ArtificialStack> = Vec::new();
            let place = match memo.entry(own) {
                Occupied(z)=>{
                    result.push(*z.get());
                    continue;
                }
                Vacant(z)=>{
                    let place = self.get_placeholder();
                    *z.insert(place)
                }
            };
            let mut outertrav = getmergedvl(self,own,&pools,&ownership);
            let (innertoken,intv) = outertrav.next().unwrap();
            stack.push(ArtificialStack{
                outercollect:Vec::new(),
                innercollect:Vec::new(),
                outertrav,
                innertoken,
                innertrav:intv,
                place,
            });
            //unevaluated gets cloned into a state besides unevaluated.
            while stack.len()>0 {
                let x = stack.last_mut().unwrap();
                loop {
                    if let Some(subl) = x.innertrav.pop() {
                        match if pools[subl].0.contains(&0) {Some(0)} else {memo.get(&subl).copied()} {
                            Some(y)=>{x.innercollect.push(y);continue;}
                            None=>{
                                let mut outertrav = getmergedvl(self,subl,&pools,&ownership);
                                if let Some((innertoken,intv)) = outertrav.next() {
                                    let place = self.get_placeholder();
                                    memo.insert(subl,place);
                                    x.innertrav.push(subl);
                                    stack.push(ArtificialStack{
                                        outercollect:Vec::new(),
                                        innercollect:Vec::new(),
                                        outertrav,
                                        innertoken,
                                        innertrav:intv,
                                        place,
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
                        let rpv = if ff.outercollect.len()==0 {panic!()} else {self.insert_into_placeholder(ff.outercollect,ff.place)};
                        match stack.last() {
                            Some(x)=>{
                                if rpv != ff.place {
                                    let fl = *x.innertrav.last().unwrap();
                                    memo.insert(fl,rpv);//harmlessly replace old value
                                }
                            }
                            None=>{
                                if rpv != ff.place {
                                    memo.insert(own,rpv);//harmlessly replace old value
                                }
                                result.push(rpv);
                            }
                        }
                        break;
                    }
                }
            }
        }
        // panic!();
        if result.len()==0 {return None}
        if result.len()==1 {return Some(result[0])}
        let mut deps:Vec<(usize,Vec<usize>)> = Vec::new();
        for s in result {deps.extend(self.paths[s].iter().cloned())}
        return Some(self.get_ntfa(deps));
    }

}



#[derive(Clone,Debug)]
pub struct SolutionStatus {
    dsl:Dsl,
    size:usize,
    value:Vec<Option<usize>>,
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
                let u:Option<Vec<usize>> = ex[0][i].map(|z|m[i].recursion.get(&z).map(|x|x.iter().copied()).into_iter().flatten().collect());
                u
            });
            let mut cart : Vec<(_,Vec<Option<usize>>)> = vec![(mapping,Vec::new())];//I hate n-ary cartesian products
            for (bin,brow) in biz.enumerate() {
                if let Some(brow) = brow {
                    let mut buf = Vec::new();
                    if brow.len()==0 {return Vec::new()}
                    for (cmap,c) in cart {
                        'defeat: for b in brow.iter() {
                            let mut cmcl = cmap.clone();
                            if *b != 0 {
                                if let Some(bex) = ex[0][bin] {
                                    match &mut cmcl {
                                        None=>{
                                            let mut hm=HashMap::new();
                                            hm.insert(bex,*b);
                                            cmcl=Some(Rc::new(hm));
                                        },
                                        Some(x)=> match Rc::make_mut(x).entry(bex) {
                                            Vacant(hole) => {hole.insert(*b);}
                                            Occupied(spot) => {
                                                if *spot.get() != *b {continue 'defeat;}
                                            }
                                        }
                                    }
                                }
                            }
                            let mut cl = c.clone();
                            cl.push(Some(*b));
                            buf.push((cmcl,cl));
                        }
                    }
                    cart=buf;
                } else {
                    for (_,c) in cart.iter_mut() {c.push(None);}
                }
            }
            for (mapping,value) in cart {
                result.push(SolutionStatus {
                    dsl:dsl.clone(),size,value,mapping
                })
            }
        } else if a==9 {
            let value:Vec<Option<usize>> = (0..m.len()).map(|i|{
                ex[0][i].and_then(|z|match &builder.values[z].0 {
                    LValue(_)=>ex[1][i],
                    RValue(_)=>ex[2][i],
                    _=>None
                })
            }).collect();
            result.push(SolutionStatus {
                dsl,size,value,mapping
            })
        } else {
            let value:Vec<Option<usize>> = (0..m.len()).map(|i|{
                ex.iter().map(|x|x[i]).try_fold(Vec::new(),|mut acc,x|{
                    if let Some(x)=x {
                        acc.push(x);Some(acc)
                    } else {None}
                }).and_then(|z|m[i].remap.get(&(a,z))).copied()
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
    // truthiness:HashMap<usize,bool>,
    remap:HashMap<(usize,Vec<usize>),usize>
}
impl ValueMapper {
    fn new()->Self {
        ValueMapper {
            recursion:HashMap::new(),
            // truthiness:HashMap::new(),
            remap:HashMap::new()
        }
    }
}

// #[derive(Clone,PartialOrd,PartialEq,Ord,Eq,Hash)]
// pub enum InvType {
//     BaseType(usize),
//     FstType(Box<InvType>),
//     SndType(Box<InvType>),
//     LType(Box<InvType>),
//     RType(Box<InvType>),
//     SomeLR,
//     Unknown
// }
// use InvType::{*};
// impl InvType {
//     fn canbe(&self,token:usize,builder:&ExpressionBuilder)->bool {
//         match (self,&builder.types[token]) {
//             (Unknown,_)=>true,
//             (SomeLR,PairType(_,_))=>true,
//             (SomeLR,_)=>false,
//             (BaseType(i),_)=>*i==token,
//             (FstType(i),PairType(a,_))=>i.canbe(*a,builder),
//             (SndType(i),PairType(_,a))=>i.canbe(*a,builder),
//             (LType(i),LRType(a,_))=>i.canbe(*a,builder),
//             (RType(i),LRType(_,a))=>i.canbe(*a,builder),
//             _=>false
//         }
//     }
//     fn over(&self,token:usize,index:usize,builder:&NTFABuilder,ex:&ExpressionBuilder)->InvType {
//         match (self,token,index) {
//             (_,9,0)=>SomeLR,
//             (x,9,1|2)=>x.clone(),
//             (FstType(x),2,0)=>*x.clone(),
//             (FstType(_),2,1)=>Unknown,
//             (SndType(_),2,0)=>Unknown,
//             (SndType(x),2,1)=>*x.clone(),
//             (BaseType(x),2,0)=>BaseType(match &ex.types[*x] {PairType(a,_)=>*a,_=>{panic!()}}),
//             (BaseType(x),2,1)=>BaseType(match &ex.types[*x] {PairType(_,a)=>*a,_=>{panic!()}}),
//             (SomeLR,5,0)=>Unknown,
//             (SomeLR,6,0)=>Unknown,
//             (LType(x),5,0)=>*x.clone(),
//             (RType(x),6,0)=>*x.clone(),
//             (BaseType(x),5,0)=>BaseType(match &ex.types[*x] {LRType(a,_)=>*a,_=>{panic!()}}),
//             (BaseType(x),6,0)=>BaseType(match &ex.types[*x] {LRType(_,a)=>*a,_=>{panic!()}}),
//             (x,3,0)=>FstType(Box::new(x.clone())),
//             (x,4,0)=>SndType(Box::new(x.clone())),
//             (x,7,0)=>LType(Box::new(x.clone())),
//             (x,8,0)=>RType(Box::new(x.clone())),
//             (_,10,0)=>BaseType(builder.input_type),
//             (Unknown,w,_) if w<11 =>Unknown,
//             (_,w,a)=>BaseType(ex.functions[w-11].argtypes[a])
//         }
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

    pub fn debug_is_accepting_run(&self,ntfa:usize,d:&Dsl,ex:&ExpressionBuilder)->bool {
        let (dslf,dsla) = match d {
            AccessStack(0)=>(1,Vec::new()),
            Lside(a)=>(5,vec![*a.clone()]),
            Rside(a)=>(6,vec![*a.clone()]),
            Pair(a,b)=>(2,vec![*a.clone(),*b.clone()]),
            BaseValue(x)=>match &ex.values[*x].0 {
                PairValue(a,b)=>(2,vec![BaseValue(*a),BaseValue(*b)]),
                LValue(a)=>(5,vec![BaseValue(*a)]),
                RValue(a)=>(6,vec![BaseValue(*a)]),
                UnitValue=>(0,Vec::new()),
                _=>panic!()
            },
            SwitchValue(c,a,b)=>(9,vec![*c.clone(),*a.clone(),*b.clone()]),
            LUndo(a)=>(7,vec![*a.clone()]),
            RUndo(a)=>(8,vec![*a.clone()]),
            LeftValue(a)=>(3,vec![*a.clone()]),
            RightValue(a)=>(4,vec![*a.clone()]),
            _=>panic!()
        };
        for (f,a) in self.paths[ntfa].iter() {
            if *f==dslf {
                if dsla.iter().zip(a.iter()).all(|(da,fa)|
                    self.debug_is_accepting_run(*fa,da,ex)
                ) {return true;}
            }
        } false
    }

}

#[derive(Default)]
pub struct PartialNTFA {
    pub rules:HashMap<usize,Vec<(usize,Vec<usize>)>>,
    occurances:HashMap<usize,HashSet<usize>>,
    maxins:usize,
    vm:ValueMapper
}
impl PartialNTFA {

    // pub fn debug_is_accepting_run(&self,d:&Dsl,ex:&ExpressionBuilder,accstates:&HashSet<usize>)->bool {
    //     if accstates.len()==0 {return false;}
    //     let (dslf,dsla) = match d {
    //         AccessStack(0)=>(1,Vec::new()),
    //         Lside(a)=>(5,vec![*a.clone()]),
    //         Rside(a)=>(6,vec![*a.clone()]),
    //         Pair(a,b)=>(2,vec![*a.clone(),*b.clone()]),
    //         BaseValue(x)=>match &ex.values[*x].0 {
    //             PairValue(a,b)=>(2,vec![BaseValue(*a),BaseValue(*b)]),
    //             LValue(a)=>(5,vec![BaseValue(*a)]),
    //             RValue(a)=>(6,vec![BaseValue(*a)]),
    //             UnitValue=>(0,Vec::new()),
    //             _=>panic!()
    //         },
    //         SwitchValue(c,a,b)=>(9,vec![*c.clone(),*a.clone(),*b.clone()]),
    //         LUndo(a)=>(7,vec![*a.clone()]),
    //         RUndo(a)=>(8,vec![*a.clone()]),
    //         LeftValue(a)=>(3,vec![*a.clone()]),
    //         RightValue(a)=>(4,vec![*a.clone()]),
    //         _=>panic!()
    //     };
    //     for i in accstates {
    //         for (f,a) in self.rules[i].iter() {
    //             if *f==dslf {
    //                 for (da,fa) in dsla.iter().zip(a.iter()) {
    //                     let mut nstates : HashSet<usize> = HashSet::new();
    //                     if !self.debug_is_accepting_run(&da,ex,&nstates) {return false}
    //                 }
    //                 // nstates.insert(a[ia]);
    //             }
    //         }
    //     } false
    // }

    pub fn new()->Self {PartialNTFA{rules:HashMap::new(),occurances:HashMap::new(),vm:ValueMapper::new(),maxins:0}}
    pub fn add_rule(&mut self,f:usize,a:Vec<usize>,r:usize) {
        let mut m=r;
        for a in a.iter() {
            if *a>m {m=*a;}
            self.occurances.entry(*a).or_default().insert(r);
        }
        if m>=self.maxins {self.maxins=m+1;}
        if f==10 {
            self.vm.recursion.entry(a[0]).or_default().insert(r);
        } else {
            self.vm.remap.insert((f,a.clone()),r);
        }
        self.rules.entry(r).or_default().push((f,a));
    }
    pub fn determinize(&mut self) {
        let mut memo : HashMap<Vec<usize>,usize> = HashMap::new();
        let mut invmemo : HashMap<usize,Vec<usize>> = HashMap::new();
        let mut stack : Vec<((usize,Vec<usize>),HashSet<usize>)> = self.vm.recursion.iter().filter_map(|(a,bs)|
            if bs.len()<2 {None}
            else {Some(((10,vec![*a]),bs.clone()))}
        ).collect();
        while let Some(((f,a),bs)) = stack.pop() {
            let mut vv : Vec<usize> = bs.iter().map(|z|invmemo.get(z).cloned().unwrap_or(vec![*z])).flatten().collect();
            vv.sort_unstable();
            vv.dedup();
            let (early,nval) = match memo.entry(vv) {
                Occupied(z)=>(true,*z.get()),
                Vacant(z)=>{
                    let nval=self.maxins;self.maxins+=1;
                    invmemo.insert(nval,z.key().clone());
                    z.insert(nval);
                    (false,nval)
                }
            };
            // println!("{:?}",vv);
            self.rules.entry(nval).or_default().push((f,a.clone()));
            for a in a.iter() {
                self.occurances.entry(*a).or_default().insert(nval);
            }
            // println!("one {:?} {:?} {:?}",f,a,bs);
            for b in bs.iter() {
                self.rules.get_mut(b).unwrap().retain(|y|y.0 != f || y.1 != a);
            }
            if early {continue}
            let mut allocc = HashSet::new();
            let mut conflictcheck : HashMap<(usize,Vec<usize>),HashSet<usize>> = HashMap::new();
            for b in bs.iter() {
                allocc.extend(self.occurances.get(b).map(|x|x.iter().copied()).into_iter().flatten());
                if let Some(zs)=self.occurances.get(b) {
                    for z in zs {
                        let rows = self.rules.get_mut(z).unwrap();
                        let mut i=0;
                        while i<rows.len() {
                            for j in 0..rows[i].1.len() {
                                if rows[i].1[j] == *b {
                                    let mut nc = rows[i].clone();
                                    nc.1[j]=nval;
                                    conflictcheck.entry(nc.clone()).or_default().insert(*z);
                                    rows.push(nc);
                                }
                            }
                            i+=1;
                        }
                        rows.sort_unstable();
                        rows.dedup();
                    }
                }
            }
            self.occurances.insert(nval,allocc);
            // if conflictcheck.iter().any(|(_,b)|b.len()>=2) {
            //     panic!("two {:?}",conflictcheck.into_iter().filter(|(_,b)|b.len()>=2).collect::<Vec<_>>() );
            // }
            stack.extend(conflictcheck.into_iter().filter(|(_,b)|b.len()>=2));
        }
    }
    pub fn convert(self,builder:&mut NTFABuilder,accstates:&Vec<usize>)->(Vec<usize>,ValueMapper) {
        #[derive(Debug)]
        struct ArtificialStack {
            outercollect: Vec<(usize,Vec<usize>)>,
            innercollect: Vec<usize>,
            outertrav: IntoIter<(usize,Vec<usize>)>,
            innertrav: Vec<usize>,
            innertoken: usize,
            // target: usize,
            place: usize,
            // types: InvType
        }
        let mut memo:HashMap<usize,Option<usize>> = HashMap::new();
        memo.insert(0,Some(0));
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
                        let rpv = if ff.outercollect.len()==0 {None} else {Some(builder.insert_into_placeholder(ff.outercollect,ff.place))};
                        // println!("\n{:?} \n{:?} \n{:?} \n{:?}\n\n",ff.outercollect,rpv,ff.place,stack);
                        match stack.last() {
                            Some(x)=>{
                                if rpv != Some(ff.place) {
                                    let fl = *x.innertrav.last().unwrap();
                                    memo.insert(fl,rpv);//harmlessly replace old value
                                }
                            }
                            None=>{
                                if rpv != Some(ff.place) {
                                    memo.insert(accstate,rpv);//harmlessly replace old value
                                }
                                // builder.deplete_minification_queue();
                                if let Some(z)=rpv {
                                    builder.purge(z);
                                    result.push(z);
                                }
                            }
                        }
                        break;
                    }
                }
            }
        } (result,self.vm)


        // #[derive(PartialEq,PartialOrd,Eq,Ord,Clone,Hash,Debug)]
        // enum ConversionOption {
        //     Positive(Vec<usize>),
        //     Negative(Vec<usize>),
        //     Anything
        // }
        // use ConversionOption::{*};
        // fn merge(a:ConversionOption,b:ConversionOption)->ConversionOption {
        //     match (a,b) {
        //         (Anything,_)|(_,Anything)=>Anything,
        //         (Positive(a),Positive(b))=>Positive(dedup_merge(a,b)),
        //         (Negative(a),Negative(b))=>Negative({
        //             let j = dedup_intersect(a,b);
        //             if j.len()==0 {return Anything} else {j}
        //         }),
        //         (Positive(a),Negative(b))|(Negative(b),Positive(a))=>Negative({
        //             let j = dedup_setminus(b,a);
        //             if j.len()==0 {return Anything} else {j}
        //         })
        //     }
        // }
        // fn negate(a:ConversionOption)->Option<ConversionOption> {
        //     match a {
        //         Positive(a)=>Some(Negative(a)),
        //         Negative(a)=>Some(Positive(a)),
        //         Anything=>None
        //     }
        // }
        // fn get_inversion_ledger(builder:&NTFABuilder,ex:&ExpressionBuilder,typeset:&InvType)->Vec<(usize,usize)> {
        //     let mut oros : Vec<(usize,usize)> = vec![(3,1),(4,1),(7,1),(8,1),(9,3)];
        //     if typeset.canbe(builder.output_type,ex) {oros.push((10,1));}
        //     oros.extend(
        //         (0..ex.get_f_count()).filter_map(|ff|{
        //             let FunctionEntry {argtypes,restype,..} = &ex.functions[ff];
        //             if typeset.canbe(*restype,ex) {
        //                 Some((11+ff,argtypes.len()))
        //             } else {None}
        //         })
        //     );
        //     if typeset.canbe(builder.input_type,ex) {oros.push((1,0));}
        //     if typeset.canbe(0,ex) {oros.push((0,0));}
        //     match &typeset {
        //         Unknown=>{oros.push((2,2));}
        //         BaseType(x)=>match &ex.types[*x] {
        //             PairType(_,_)=>{oros.push((2,2));}
        //             _=>{}
        //         }
        //         FstType(_)=>{oros.push((2,2));}
        //         SndType(_)=>{oros.push((2,2));}
        //         _=>{}
        //     }
        //     match &typeset {
        //         SomeLR|Unknown=>{
        //             oros.push((5,1));
        //             oros.push((6,1));
        //         }
        //         BaseType(x)=>match &ex.types[*x] {
        //             LRType(_,_)=>{
        //                 oros.push((5,1));
        //                 oros.push((6,1));
        //             }
        //             _=>{}
        //         }
        //         LType(_)=>{oros.push((5,1));}
        //         RType(_)=>{oros.push((6,1));}
        //         _=>{}
        //     }
        //     oros.sort_unstable();
        //     oros
        // }
        // fn getmergedvl<T:Iterator<Item=usize>>(
        //     sel:&PartialNTFA,
        //     builder:&NTFABuilder,
        //     ex:&ExpressionBuilder,
        //     ind:T,
        //     negative:bool,
        //     typeset:&InvType
        // )->IntoIter<(usize,Vec<ConversionOption>)> {
        //     let mut deps:Vec<(usize,Vec<ConversionOption>)> = Vec::new();
        //     for s in ind {deps.extend(sel.rules.get(&s).into_iter().map(|ii|ii.iter().map(|(f,a)|
        //         (*f,a.iter().map(|x|if *x==0 {Anything} else {Positive(vec![*x])}).collect())
        //     )).flatten());}
        //     deps.sort_unstable();
        //     deps.dedup();
        //     // let OLDDEPS = deps.clone();
        //     let mut a=0;
        //     while a+1<deps.len() {
        //         let f = deps[a].0;
        //         let l = deps[a].1.len();
        //         let mut b=1;
        //         while deps[a+b].0==f {
        //             b+=1;
        //             if a+b>=deps.len() {break;}
        //         }
        //         for x in 0..b-1 {
        //             let mut y=x+1;
        //             while y<b {
        //                 if (0..l).all(|a2|deps[a+x].1[a2]==deps[a+y].1[a2] || deps[a+x].1[a2]==Anything || deps[a+y].1[a2]==Anything) {
        //                     let depr = take(&mut deps.remove(a+y).1);
        //                     for (rr,kk) in deps[a+x].1.iter_mut().zip(depr.into_iter()) {
        //                         if kk==Anything {*rr=Anything;}
        //                     }
        //                     b-=1;
        //                 } else {
        //                     y+=1;
        //                 }
        //             }
        //         }
        //         if b != 1 {
        //             for amt in 0..l {
        //                 let mut x=0;
        //                 while x<b {
        //                     if if let Anything = deps[a+x].1[amt] {
        //                         let mut ooc = Vec::new();
        //                         for y in 0..b {
        //                             if let Positive(k) = &deps[a+y].1[amt] {
        //                                 if (0..amt).all(|i|deps[a+y].1[i]==deps[a+x].1[i]) {
        //                                     ooc.push(k[0]);
        //                                 }
        //                             }
        //                         }
        //                         if ooc.len()>0 {
        //                             let mut rag = deps[a+x].clone();
        //                             rag.1[amt]=Negative(ooc.clone());
        //                             deps[a+x].1[amt]=Positive(ooc);
        //                             deps.insert(a+x+1,rag);
        //                             b+=1;false
        //                         } else {true}
        //                     } else {true} {
        //                         let mut y = x+1;
        //                         while y<b {
        //                             if (0..l).all(|a2|a2==amt || deps[a+x].1[a2]==deps[a+y].1[a2]) {
        //                                 let depr = replace(&mut deps.remove(a+y).1[amt],Anything);
        //                                 deps[a+x].1[amt] = merge(replace(&mut deps[a+x].1[amt],Anything),depr);
        //                                 b-=1;
        //                             } else {
        //                                 y+=1;
        //                             }
        //                         }
        //                         x+=1;
        //                     }
        //                 }
        //             }
        //         }
        //         a+=b;
        //     }
        //     if negative {
        //         let mut i=0;
        //         let mut oros : Vec<(usize,Vec<ConversionOption>)> = Vec::new();
        //         for (kf,kt) in get_inversion_ledger(builder,ex,typeset) {
        //             while i<deps.len() && deps[i].0>kf {i+=1}
        //             if i>=deps.len() {
        //                 oros.push((kf,(0..kt).map(|_|Anything).collect()));
        //                 continue;
        //             }
        //             if kt==0 {i+=1;continue;}
        //             let mut j = i+1;
        //             while j<deps.len() && deps[i].0==deps[j].0 {j+=1;}
        //             let mut stack = vec![(i,j)];
        //             'outer: while let Some((i,j))=stack.last().copied() {
        //                 let amt = stack.len()-1;
        //                 if amt==deps[i].1.len() {
        //                     loop {
        //                         let (i,j) = stack.pop().unwrap();
        //                         let amt = stack.len()-1;
        //                         if let Some(z) = deps[i..j].iter().map(|v|v.1[amt].clone()).reduce(merge).and_then(negate) {
        //                             oros.push((deps[i].0,deps[i].1[..amt].iter().cloned()
        //                                         .chain(once(z))
        //                                         .chain((amt+1..deps[i].1.len()).map(|_|Anything)).collect()));
        //                         }
        //                         match stack.last_mut() {
        //                             None=>{break 'outer;}
        //                             Some((ip,jp))=>{
        //                                 if *jp==j {continue}
        //                                 *ip=j;continue 'outer;
        //                             }
        //                         }
        //                     }
        //                 }
        //                 let mut k=i+1;
        //                 while k<j && deps[i].1[amt]==deps[k].1[amt] {k+=1;}
        //                 stack.push((i,k));
        //             }
        //             i=j;
        //         }
        //         deps = oros;
        //     }
        //     // println!("transform: {:?} => {:?}",OLDDEPS,deps);
        //     deps.sort_unstable();
        //     for (_,v) in deps.iter_mut() {
        //         v.reverse();
        //     }
        //     deps.into_iter()
        // }
        // if accstates.len()==0 {return None}
        // struct ArtificialStack {
        //     outercollect: Vec<(usize,Vec<usize>)>,
        //     innercollect: Vec<usize>,
        //     outertrav: IntoIter<(usize,Vec<ConversionOption>)>,
        //     innertrav: Vec<ConversionOption>,
        //     innertoken: usize,
        //     place: usize,
        //     types: InvType
        // }
        // let mut stack:Vec<ArtificialStack> = Vec::new();
        // let mut memo:HashMap<ConversionOption,Option<usize>> = HashMap::new();
        // memo.insert(Anything,Some(0));

        // let mut snok = accstates.iter().copied().collect::<Vec<_>>();
        // snok.sort_unstable();

        // let place = builder.get_placeholder();
        // memo.insert(Positive(snok.clone()),Some(place));
        // let intype = BaseType(builder.output_type);
        // let mut outertrav = getmergedvl(&self,builder,ex,accstates.iter().copied(),false,&intype);
        // let (innertoken,intv) = outertrav.next().unwrap();
        // stack.push(ArtificialStack{
        //     outercollect:Vec::new(),
        //     innercollect:Vec::new(),
        //     outertrav,
        //     innertoken,
        //     innertrav:intv,
        //     place,
        //     types: intype
        // });
        // loop {
        //     let x = stack.last_mut().unwrap();
        //     loop {
        //         if let Some(subl) = x.innertrav.pop() {
        //             match memo.get(&subl).copied() {
        //                 Some(Some(y))=>{x.innercollect.push(y);continue;}
        //                 Some(None)=>{x.innercollect.clear();}
        //                 None=>{
        //                     let (inn,neg) = match &subl {Anything=>panic!(),Positive(inn)=>(inn,false),Negative(inn)=>(inn,true)};
        //                     let mut outertrav = getmergedvl(&self,builder,ex,inn.iter().copied(),neg,&x.types);
        //                     if let Some((innertoken,intv)) = outertrav.next() {
        //                         let place = builder.get_placeholder();
        //                         memo.insert(subl.clone(),Some(place));
        //                         x.innertrav.push(subl);
        //                         let nn = x.types.over(x.innertoken,x.innercollect.len(),builder,ex);
        //                         stack.push(ArtificialStack{
        //                             outercollect:Vec::new(),
        //                             innercollect:Vec::new(),
        //                             outertrav,
        //                             innertoken,
        //                             innertrav:intv,
        //                             place,
        //                             types:nn
        //                         });
        //                         break;
        //                     } else {x.innercollect.clear();}
        //                 }
        //             }
        //         } else {
        //             let v = take(&mut x.innercollect);
        //             x.outercollect.push((x.innertoken,v));
        //         }
        //         if let Some((innertoken,intv))=x.outertrav.next() {
        //             x.innertoken=innertoken;
        //             x.innertrav=intv;
        //         } else {
        //             let ff = stack.pop().unwrap();
        //             let rpv = if ff.outercollect.len()==0 {None} else {Some(builder.insert_into_placeholder(ff.outercollect,ff.place))};
        //             match stack.last() {
        //                 Some(x)=>{
        //                     if rpv != Some(ff.place) {
        //                         let fl = x.innertrav.last().unwrap();
        //                         memo.insert(fl.clone(),rpv);//harmlessly replace old value
        //                     }
        //                 }
        //                 None=>{
        //                     // builder.deplete_minification_queue();
        //                     return rpv.map(|x|(x,self.vm))
        //                 }
        //             }
        //             break;
        //         }
        //     }
        // }
    }
}



