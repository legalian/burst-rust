

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
    intersect_memo:HashMap<(usize,usize),usize>,

    // closed_expr:HashSet<usize>,

    uneval_hack:Option<usize>,

    minification_queue:Vec<usize>,


    created_by_union:HashSet<usize>


    // purge_memo:HashSet<usize>
}
impl NTFABuilder {
    pub fn new()->Self {
        NTFABuilder {
            paths:Vec::new(),//inner vec must be sorted
            revhash:HashMap::new(),
            intersect_memo:HashMap::new(),
            // closed_expr:HashSet::new(),
            uneval_hack:None,
            // purge_memo:HashSet::new()
            minification_queue:Vec::new(),
            created_by_union:HashSet::new()
        }
    }
    // pub fn purge(&mut self,start:usize) {
    //     if self.purge_memo.contains(&start) {
    //         return;
    //     }
    //     self.purge_memo.insert(start);
    //     let deps = &self.paths[start];
    //     if deps.len()==0 {panic!("empty shit: {}",start)}
    //     let mut asdfj = Vec::new();
    //     for j in deps.iter() {
    //         for k in j.1.iter() {
    //             asdfj.push(*k);
    //         }
    //     }
    //     for k in asdfj {self.purge(k);}
    // }
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
                        let tmp = self.union(al[l],bl[l]);
                        deps[a+c].1[l]=tmp;
                        deps.remove(a+b);
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
    // fn all_children_closed(&self,deps: &[(usize,Vec<usize>)])->bool {
    //     deps.iter().all(|(_,x)|x.iter().all(|y|self.closed_expr.contains(y)))
    // }
    fn check_requires_further(deps: &[(usize,Vec<usize>)])->bool {
        let mut requires_further = true;
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
    pub fn deplete_minification_queue(&mut self) {
        while let Some(i) = self.minification_queue.pop() {
            self.indepth_simplify(i);
        }
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
                // if ao>1||bo>1 {println!("did a big one: {}x{} of {}",ao,bo,f);}
                a+=ao;
                b+=bo;
            }
        }
        if output.len()==0 {return None}
        self.insert_into_placeholder(output,place);
        Some(place)
    }
    pub fn union(&mut self,a:usize,b:usize) -> usize {
        let st = self.paths.len();
        let whwh : Vec<_> = self.paths[a].iter().cloned().chain(self.paths[b].iter().cloned()).collect();
        if whwh.len()==0 {panic!()}
        let vbvb = self.get_ntfa(whwh);
        if self.paths.len()!=st {
            if vbvb!=st {
                panic!("fuck");
            }
            self.created_by_union.insert(vbvb);
            if self.created_by_union.contains(&a) || self.created_by_union.contains(&b) {
                println!("repeated union: {} u {} = {};",a,b,vbvb);
            } else {
                println!("new union: {} u {} = {};",a,b,vbvb);
            }
        }
        vbvb
    }
    pub fn nary_union(&mut self,mut a:Vec<usize>) -> Option<usize> {
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
            } else {continue;}
            while let Some(x) = stack.last_mut() {
                loop {
                    if x.innertrav.len()>0 {
                        if let Some(y) = {
                            if x.innertrav[0]==0 {
                                builder.uneval_hack
                            } else {
                                memo.get(&x.innertrav[0]).copied()
                            }
                        } {
                            x.innercollect.push(y);
                            x.innertrav=&x.innertrav[1..];
                            continue;
                        } else {
                            if let Some(y) = self.rules.get(&x.innertrav[0]) {
                                let place = builder.get_placeholder();
                                if x.innertrav[0]==0 {
                                    builder.uneval_hack = Some(place);
                                    // builder.simplification_memo.insert(place,place);
                                } else {
                                    memo.insert(x.innertrav[0],place);
                                }
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
                        let rpv = builder.insert_into_placeholder(ff.outercollect,ff.place);
                        match stack.last() {
                            Some(x)=>{
                                if rpv != ff.place {
                                    if x.innertrav[0]==0 {panic!("what?")}
                                    memo.insert(x.innertrav[0],rpv);//harmlessly replace old value
                                }
                            }
                            None=>{
                                memo.insert(*acc,rpv);//harmlessly replace old value
                                accepting.push(rpv);
                            }
                        }
                        break;
                    }
                }
            }
        }
        match builder.nary_union(accepting) {
            Some(x) => {
                builder.deplete_minification_queue();
                Some((x,self.vm))
            }
            None=>None
        }
    }
}



