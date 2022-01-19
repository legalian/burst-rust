

use std::collections::HashMap;
use std::collections::HashSet;
// use std::collections::VecDeque;
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



