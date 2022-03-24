use crate::nftabuilder::{*};
use crate::nfta::{*};
use crate::acceptingrun::{*};
use crate::dsl::{*};
use std::collections::{*};
use TermClassification::{*};
use Transition::{*};
use std::collections::hash_map::Entry::{*};
use TypeMapType::{*};
use ProcType::{*};
use ProcValue::{*};
use std::rc::Rc;
use std::mem::{take};
use std::cmp::Ordering;


// predicate language:
// AND (obvious)
// func(self)
// func(left(self))
// func(right(self))
// func(inl(self))
// func(inr(self))
// L+func(unl(self))
// R+func(unr(self))
// func((self,const))
// func((const,self))

// ^^^ you fucking got it


// "yeah, well, the MEASURE(a(b(c(i(output))))) is a [0,6) and it should be a 6. new predicate: MEASURE(a(b(c(i(x)))))"
// "or MEASURE(i^-1(c^-1(b^-1(a^-1(x)))))? for inverse? or  is the other one for inverse? make a punnett square for that and the inverse first-child-to-betray-set solution thingy"


// MAKE PREDICATES THEMSELVES CONTAIN DSL

// PUT IT IN MAIN.RS THAT DSLS SHOULD BE RC'ED


// stubby:
//     partial eval forward (Vec<Predlist>,Transition -> Predlist)
//     alpha (Predlist,universe -> Predlist)
//     widening (&mut universe,target:Predlist,children:Vec<Predlist> -> Vec<Predlist>)



// f ( vec<predicate> ) -> any   [at first]
// f ( vec<concrete predicate> ) -> actual

// ^^^^ that should take care of initial building. Plus alpha, which in this case isn't much.

// Then, you get an accepting run. Recursively widen it, as below. You can widen yourself and add yourself to
//     the output list of predicates before considering children. Use the worklist impl, as stated in the paper.

// just need to refine all your predicates. Widen the one on the very end, and only widen the ones that come before (recursively)
// if they still logically imply the next node.
// at first, this is pretty much just going to mean widening the root/accepting node i suppose.

// widening func: it really depends on f. You have your minimal unwidened spec that can be simplified (and ought to be if the result is EQ, which it is)
//     arbitrary func: can't widen your arguments. sorry.
//     just throw a stub together. you'll see what to do after you have it stubbed. same goes for the other 2.

#[derive(Clone,PartialEq,Eq,Hash,Debug)]
enum SkeletonFilterNode {
    Constfilt(usize,Vec<SkeletonFilter>),
    Exactfilt(usize),
}
use SkeletonFilterNode::{*};
type SkeletonFilter=Vec<SkeletonFilterNode>;
fn merge(a:SkeletonFilter,b:SkeletonFilter)->SkeletonFilter {
    let mut sk = a;
    'outer: for c in b {
        match c {
            Exactfilt(_)=>{
                if !sk.contains(&c) {sk.push(c);}
            }
            Constfilt(cx,cl)=>{
                for k in sk.iter_mut() {
                    if let Constfilt(x,l) = k {
                        if *x==cx {
                            *l = cl.into_iter().zip(take(l)).map(|(x,y)|merge(x,y)).collect();
                            continue 'outer;
                        }
                    }
                }
                sk.push(Constfilt(cx,cl));
            }
        }
    } sk
}


#[derive(Clone,PartialEq,Eq,Hash,Debug)]
pub enum Skeleton {
    Constsk(usize,Vec<Skeleton>),
    Exact(usize),
    Hole
}
use Skeleton::{*};
impl Skeleton {
    fn accepts(&self,b:usize,builder:&ExpressionBuilder)->bool {
        match self {
            Hole=>true,
            Exact(e)=>*e==b,
            Constsk(a,al)=>match &builder.values[b].0 {
                Const(b,bl)=>{
                    if a != b {return false;}
                    let bl=bl.clone();
                    al.iter().zip(bl.iter()).all(|(a,b)|a.accepts(*b,builder))
                }
                _=>panic!()
            }
        }
    }
    fn filter(self,other:&SkeletonFilter,builder:&ExpressionBuilder)->Skeleton {
        match self {
            Hole=>Hole,
            Exact(n)=>if other.contains(&Exactfilt(n)) {Exact(n)} else {
                match &builder.values[n].0 {
                    Const(b,bl)=>{
                        for k in other.iter() {
                            if let Constfilt(a,al) = k {
                                if *b==*a {
                                    return Constsk(*a,bl.into_iter().zip(al.iter()).map(|(b,a)|Exact(*b).filter(a,builder)).collect());
                                }
                            }
                        } Hole
                    }
                    _=>panic!()
                }
            }
            Constsk(a,al)=>{
                for k in other.iter() {
                    if let Constfilt(b,bl) = k {
                        if *b==a {
                            return Constsk(a,al.into_iter().zip(bl.iter()).map(|(a,b)|a.filter(b,builder)).collect());
                        }
                    }
                } Hole
            }
        }
    }
    pub fn common(self,other:Skeleton,builder:&mut ExpressionBuilder)->Skeleton {
        match (self,other) {
            (Constsk(a,al),Constsk(b,bl))=>if a==b {
                Constsk(a,al.into_iter().zip(bl.into_iter()).map(|(a,b)|{
                    a.common(b,builder)
                }).collect())
            } else {Hole},
            (Exact(a),Exact(b))=>if a==b {Exact(a)} else {Hole},
            (Exact(a),Constsk(b,bl))=>{
                match &builder.values[a].0 {
                    Const(a,al)=>{
                        let al=al.clone();
                        if *a != b {return Hole;}
                        Constsk(*a,bl.into_iter().zip(al).map(|(b,a)|b.common(Exact(a),builder)).collect())
                    }
                    _=>panic!()
                }
            }
            (Constsk(a,al),Exact(b))=>{
                match &builder.values[b].0 {
                    Const(b,bl)=>{
                        let bl=bl.clone();
                        if *b != a {return Hole;}
                        Constsk(*b,al.into_iter().zip(bl).map(|(a,b)|a.common(Exact(b),builder)).collect())
                    }
                    _=>panic!()
                }
            }
            (_,Hole)|(Hole,_)=>Hole,
        }
    }
    fn intersect(self,other:Skeleton,builder:&mut ExpressionBuilder)->Option<Skeleton> {
        match (self,other) {
            (Constsk(a,al),Constsk(b,bl))=>if a==b {
                let mut h=true;
                let ol = al.len();
                let z : Vec<_> = al.into_iter().zip(bl.into_iter()).filter_map(|(a,b)|{
                    let g = a.intersect(b,builder);
                    if let Some(Exact(_))=g {} else {h=false;} g
                }).collect();
                if z.len()!=ol {return None;}
                if h {return Some(Exact(builder.get_constructed(a,z.into_iter().map(|y|match y {Exact(x)=>x,_=>panic!()}).collect())))}
                Some(Constsk(a,z))
            } else {None},
            (Exact(a),Exact(b))=>if a==b {Some(Exact(a))} else {None},
            (Exact(a),Constsk(b,bl))=>{
                match &builder.values[a].0 {
                    Const(a,al)=>{
                        let al=al.clone();
                        if *a != b {return None;}
                        if bl.into_iter().zip(al).any(|(b,a)|b.intersect(Exact(a),builder).is_none()) {return None;}
                    }
                    _=>panic!()
                } Some(Exact(a))
            }
            (Constsk(a,al),Exact(b))=>{
                match &builder.values[b].0 {
                    Const(b,bl)=>{
                        let bl=bl.clone();
                        if *b != a {return None;}
                        if al.into_iter().zip(bl).any(|(a,b)|a.intersect(Exact(b),builder).is_none()) {return None;}
                    }
                    _=>panic!()
                } Some(Exact(b))
            }
            (a,Hole)=>Some(a),
            (Hole,b)=>Some(b)
        }
    }
}

impl PartialOrd for Skeleton {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self,other) {
            (Hole,Hole)=>Some(Ordering::Equal),
            (Hole,_)=>Some(Ordering::Less),
            (_,Hole)=>Some(Ordering::Greater),
            (Constsk(ax,ay),Constsk(bx,by)) => Some((ax,ay).cmp(&(bx,by))),
            (Constsk(_,_),_)=>Some(Ordering::Less),
            (_,Constsk(_,_))=>Some(Ordering::Greater),
            (Exact(a),Exact(b)) => Some(a.cmp(&b)),
            // (Exact(_),_)=>Some(Ordering::Less),
            // (_,Exact(_))=>Some(Ordering::Greater),
        }
    }
}
impl Ord for Skeleton {
    fn cmp(&self,other:&Self) -> Ordering {
        match (self,other) {
            (Hole,Hole)=>Ordering::Equal,
            (Hole,_)=>Ordering::Less,
            (_,Hole)=>Ordering::Greater,
            (Constsk(ax,ay),Constsk(bx,by)) => (ax,ay).cmp(&(bx,by)),
            (Constsk(_,_),_)=>Ordering::Less,
            (_,Constsk(_,_))=>Ordering::Greater,
            (Exact(a),Exact(b)) => a.cmp(&b),
            // (Exact(_),_)=>Ordering::Less,
            // (_,Exact(_))=>Ordering::Greater,
        }
    }
}



#[derive(Clone,PartialEq,Eq,Hash,Debug)]
enum Predicate {
    Equal(Dsl,Skeleton),
    MeasureRange(Dsl,usize,Option<usize>),
}
use Predicate::{*};


impl PartialOrd for Predicate {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self,other) {
            (Equal(ax,ay),Equal(bx,by)) => Some((ax,ay).cmp(&(bx,by))),
            (Equal(_,_),_)=>Some(Ordering::Less),
            (_,Equal(_,_))=>Some(Ordering::Greater),
            (MeasureRange(ax,ay,az),MeasureRange(bx,by,bz)) => Some((ax,ay,az).cmp(&(bx,by,bz))),
            // (MeasureRange(_,_,_),_)=>Some(Ordering::Less),
            // (_,MeasureRange(_,_,_))=>Some(Ordering::Greater),
        }
    }
}
impl Ord for Predicate {
    fn cmp(&self,other:&Self) -> Ordering {
        match (self,other) {
            (Equal(ax,ay),Equal(bx,by)) => (ax,ay).cmp(&(bx,by)),
            (Equal(_,_),_)=>Ordering::Less,
            (_,Equal(_,_))=>Ordering::Greater,
            (MeasureRange(ax,ay,az),MeasureRange(bx,by,bz)) => (ax,ay,az).cmp(&(bx,by,bz)),
            // (MeasureRange(_,_,_),_)=>Ordering::Less,
            // (_,MeasureRange(_,_,_))=>Ordering::Greater,
        }
    }
}



struct Alphabet {
    ranges:HashMap<(usize,Dsl),Vec<(usize,Option<usize>)>>,
    equals:HashMap<(usize,Dsl),SkeletonFilter>,
}

// Rooted() unique
// MeasureRange(x,min,max) unique given x
// Equal(x,whatever) unique given x


type Predlist = Vec<Predicate>;
impl AcceptableMap<usize,Predlist> for Vec<(Predlist,usize,TermClassification)> {
    fn rem(&mut self,a:usize)->Predlist {take(&mut self[a].0)}
    fn def()->usize {0}
}
fn belongs(a:&Predicate,b:usize,builder:&mut ExpressionBuilder)->bool {
    match a {
        Equal(x,sk) => match builder.evaluate_solitary(x,b) {
            None=>false,
            Some(v)=>sk.accepts(v,builder)
        },
        MeasureRange(x,min,max) => match builder.evaluate_solitary(x,b) {
            None=>false,
            Some(v)=>{
                if v<*min {return false;}
                if let Some(z)=*max {
                    if v>=z {return false;}
                } true
            }
        }
    }
}
impl SpecLike for Predlist {
    fn get_narrow(&self)->Option<usize> {
        if self.len()==1 {
            if let Equal(Dsl::AccessStack(0),Exact(c)) = self[0] {
                return Some(c);
            }
        } None
    }
    fn moregeneral(&self,other:&Self,builder:&mut ExpressionBuilder)->bool {
        if self.len()==0 {return true;}
        if other.len()==0 {return false;}
        match self.intersection(other,builder) {
            None=>false,
            Some(z)=>&z==other
        }
    }
    fn intersection(&self,other:&Self,builder:&mut ExpressionBuilder)->Option<Self> {
        if self.len()==0 {return Some(other.clone());}
        if other.len()==0 {return Some(self.clone());}

        let mut tself : Vec<Predicate> = if self.len()<other.len() {other.clone()} else {self.clone()};
        let mut mergestack : Vec<Predicate> = if self.len()<other.len() {self.clone()} else {other.clone()};
        'outer: while let Some(mut b) = mergestack.pop() {
            for a in (0..tself.len()).rev() {
                match (&tself[a],b) {
                    (MeasureRange(Dsl::AccessStack(0),_,Some(max)),Equal(Dsl::AccessStack(0),v))=>{
                        let mut max=*max;
                        let mut w=&v;
                        loop {
                            match w {
                                Constsk(_,k)=>{
                                    if max<2 {return None;}
                                    max-=1;
                                    w=&k[0];
                                }
                                _=>{break;}
                            }
                        }
                        b=Equal(Dsl::AccessStack(0),v);
                    }
                    (Equal(ax,ac),Equal(bx,bc))=>if *ax==bx {
                        if let Some(z) = ac.clone().intersect(bc.clone(),builder) {
                            b=Equal(ax.clone(),z);
                            tself.remove(a);
                        } else {return None;}
                    } else {match (builder.nonvariablereasoning(ax,&bx,0,&bc),builder.nonvariablereasoning(&bx,ax,0,ac)) {
                        ((_,_,false),(_,_,false))=>{b=Equal(bx,bc)},
                        ((_,_,false),(bn,_,true))=>{
                            if !decompose_equal(bn,bc,&mut mergestack,builder) {return None;}
                            continue 'outer;
                        },
                        ((an,_,true),(_,_,false))=>{
                            let ac = match tself.remove(a) {Equal(_,ac)=>ac,_=>panic!()};
                            if !decompose_equal(an,ac,&mut mergestack,builder) {return None;}
                            b=Equal(bx,bc)
                        },
                        _=>panic!()
                    }},
                    (Equal(ax,ac),MeasureRange(bx,bmin,bmax))=>match builder.nonvariablereasoning(&bx,ax,0,ac) {
                        (_,_,false)=>{b=MeasureRange(bx,bmin,bmax)},
                        (bn,_,true)=>{
                            if !decompose_measure(bn,bmin,bmax,&mut mergestack,builder) {return None;}
                            continue 'outer;
                        }
                    },
                    (MeasureRange(ax,amin,amax),Equal(bx,bc))=>match builder.nonvariablereasoning(ax,&bx,0,&bc) {
                        (_,_,false)=>{b=Equal(bx,bc)},
                        (an,_,true)=>{
                            if !decompose_measure(an,*amin,*amax,&mut mergestack,builder) {return None;}
                            tself.remove(a);
                            b=Equal(bx,bc);
                        }
                    },
                    (MeasureRange(ax,amin,amax),MeasureRange(bx,bmin,bmax))=>if *ax==bx {
                        let min=if *amin<bmin {*amin} else {bmin};
                        let max=if let Some(amax)=*amax {
                            if let Some(bmax)=bmax {
                                Some(if amax<bmax {amax} else {bmax})
                            } else {Some(amax)}
                        } else {bmax};
                        if let Some(max)=max {
                            if min>=max {return None;}
                        }
                        b=MeasureRange(ax.clone(),min,max);
                        tself.remove(a);
                    } else {b=MeasureRange(bx,bmin,bmax)}
                }
            }
            tself.push(b);
        }
        tself.sort_unstable();
        Some(tself)
    }
}


fn decompose_equal(a:Dsl,c:Skeleton,out:&mut Vec<Predicate>,builder:&mut ExpressionBuilder)->bool {
    let mut stack = vec![(a,c)];
    while let Some((u,spec))=stack.pop() {
        match u {
            Dsl::BaseValue(y)=>{ if y==0 {continue;}; if spec.accepts(y,builder) {return false;} },
            Dsl::Construct(a,v)=>match spec {
                Hole=>{}
                Constsk(b,bl)=>{
                    if b != a {return false;}
                    stack.extend(v.into_iter().zip(bl.into_iter()));
                }
                Exact(e)=>match &builder.values[e].0 {
                    Const(j,n)=>{
                        if *j != a {return false;}
                        stack.extend(v.into_iter().zip(n.iter().copied().map(|k|Exact(k))));
                    }
                    _=>panic!()
                }
            }
            Dsl::Deconstruct(cstr,i,w)=>{
                let mut v = vec![Hole;builder.constructors[cstr].argtypes.len()];
                v[i]=spec;
                stack.push((*w,Constsk(cstr,v)));
            }
            u=>{out.push(Equal(u,spec));}
        }
    } true
}
fn decompose_measure(mut a:Dsl,mut min:usize,mut max:Option<usize>,out:&mut Vec<Predicate>,builder:&mut ExpressionBuilder)->bool {
    loop {
        match a {
            Dsl::BaseValue(y)=>{
                if y==0 {continue;};
                let number = builder.values[y].1-1;
                if number < min {return false;}
                if let Some(max) = max {
                    if number >= max {return false;}
                }
                return true;
            },
            Dsl::Deconstruct(_,_,v)=>{
                min+=1;
                if let Some(z) = &mut max {*z+=1;}
                a=*v;
            }
            Dsl::Construct(_,mut v)=>{
                if v.len()==0 {
                    if min>0 {return false;}
                    return true;
                } else {
                    if min>0 {min-=1;}
                    if let Some(z) = &mut max {
                        *z-=1;
                        if *z == min {return false;}
                        if *z == min+1 {
                            let bb = builder.force_get_nat();
                            let os = builder.get_constructors_for(bb);
                            let mut base = builder.get_constructed(os[0],Vec::new());
                            for _ in 0..min {base = builder.get_constructed(os[1],vec![base]);}
                            return decompose_equal(v.remove(0),Exact(base),out,builder);
                        }
                    }
                    a=v.remove(0);
                }
            }
            u=>{out.push(MeasureRange(u,min,max));return true;}
        }
    }
}
fn predl_transform(s:&Predlist,constr:bool,cstr:usize,index:usize,builder:&mut ExpressionBuilder)->Option<Predlist> {
    let mut tself : Vec<_> = Vec::new();
    for x in s.iter() {
        match x {
            Equal(x,spec)=>{
                let a = if constr {
                    let mut v = vec![Dsl::BaseValue(0);builder.constructors[cstr].argtypes.len()];
                    v[index]=Dsl::AccessStack(0);
                    Dsl::Construct(cstr,v)
                } else {
                    Dsl::Deconstruct(cstr,index,Box::new(Dsl::AccessStack(0)))
                };
                let u = builder.substitute(x,0,0,Rc::new(vec![(vec![a.clone()],0)]));
                if !decompose_equal(u,spec.clone(),&mut tself,builder) {return None;}
            }
            MeasureRange(x,min,max)=>{
                let a = if constr {
                    let mut v = vec![Dsl::BaseValue(0);builder.constructors[cstr].argtypes.len()];
                    v[index]=Dsl::AccessStack(0);
                    Dsl::Construct(cstr,v)
                } else {
                    Dsl::Deconstruct(cstr,index,Box::new(Dsl::AccessStack(0)))
                };
                let u = builder.substitute(x,0,0,Rc::new(vec![(vec![a.clone()],0)]));
                if !decompose_measure(u,*min,*max,&mut tself,builder) {return None;}
            }
        }
    }
    tself.sort_unstable();
    Some(tself)
}

//detect collisions between equal and range?
//not allowed: [x,x), [x,x+1), Rooted(Hole), Equal(AccessStack(x),c), 
//


impl NFTABuilder<Predlist> {
    pub fn build_afta(
        &mut self,
        builder:&mut ExpressionBuilder,
        input:Predlist,
        output:Predlist,
        alphabet:&mut Alphabet,
        interp:usize
    )->Vec<usize> {
        let mut processed_rel : HashMap<usize,Vec<usize>> = HashMap::new();//type:val,size
        let mut queue : Vec<(Predlist,usize,TermClassification)> = Vec::new();
        let mut visited : HashMap<(Predlist,usize,TermClassification),usize> = HashMap::new();
        let mut accepting_states = Vec::new();
        #[inline(always)]
        fn expand(
            alphabet : &Alphabet,
            builder : &mut ExpressionBuilder,
            amp : Predlist,
            ty : usize
        ) -> Predlist {

            // struct Alphabet {
            //     ranges:HashMap<(usize,Dsl),Vec<(usize,usize)>>,
            //     equals:HashMap<(usize,Dsl),SkeletonFilter>,
            // }

            let mut mm : Vec<_> = amp.into_iter().filter_map(|y|match y {
                Equal(x,r)=>{
                    let idex = (ty,x);
                    if let Some(skf) = alphabet.equals.get(&idex) {
                        match r.filter(skf,builder) {
                            Hole=>None,
                            z=>Some(Equal(idex.1,z))
                        }
                    } else {
                        if let (Some(z),Exact(e))=(alphabet.ranges.get(&idex),r) {
                            let number = builder.values[e].1-1;
                            if let Some((min,max)) = z.iter().find(|(min,max)|{
                                if number<*min {return false;}
                                if let Some(max)=*max {
                                    if number>=max {return false;}
                                } true
                            }) {
                                Some(MeasureRange(idex.1,*min,*max))
                            } else {None}
                        } else {None}
                    }
                }
                MeasureRange(x,lmin,lmax)=>{
                    let idex = (ty,x);
                    if let Some(z) = alphabet.ranges.get(&idex){
                        if let Some((min,max)) = z.iter().find(|(min,max)|{
                            if lmin<*min {return false;}
                            match (lmax,*max) {
                                (Some(lmax),Some(max))=>lmax<=max,
                                (None,Some(_))=>false,
                                _=>true
                            }
                        }) {
                            Some(MeasureRange(idex.1,*min,*max))
                        } else {None}
                    } else {None}
                }
            }).collect();
            mm.sort_unstable();
            mm.dedup();
            mm
        }
        #[inline(always)]
        fn alpha(
            alphabet : &Alphabet,
            builder : &mut ExpressionBuilder,
            queue : &mut Vec<(Predlist,usize,TermClassification)>,
            visited : &mut HashMap<(Predlist,usize,TermClassification),usize>,
            amp : Predlist,
            ty : usize,
            class : TermClassification,
        )->usize {
            let predlist = expand(alphabet,builder,amp,ty);
            if predlist.len()==0 {return 0;}
            match visited.entry((predlist,ty,class)) {
                Occupied(x)=>*x.get(),
                Vacant(x)=>{
                    let qlen=queue.len();
                    queue.push(x.key().clone());qlen
                }
            }
        }
        #[inline(always)]
        fn transfix(
            alphabet : &Alphabet,
            builder : &mut ExpressionBuilder,
            queue : &mut Vec<(Predlist,usize,TermClassification)>,
            visited : &mut HashMap<(Predlist,usize,TermClassification),usize>,
            res : &mut PartialNFTA<usize>,
            f : Transition,
            args : Vec<usize>,
            ty : usize,
        ) {
            match f {
                f@Destruct(cstr,i)=>{
                    if let Some(z) = predl_transform(&queue[args[0]].0,true,cstr,i,builder) {
                        res.add_rule(f,args,alpha(alphabet,builder,queue,visited,z,ty,Elimination));
                    }
                }
                f@Construct(cstr)=>{
                    let mut zz = Vec::new();
                    for (i,a) in args.iter().enumerate() {
                        let z = match predl_transform(&queue[*a].0,false,cstr,i,builder) {
                            Some(z)=>z,None=>{return;}
                        };
                        if zz.len()==0 {zz=z}
                        else {zz = match Predlist::intersection(&zz,&z,builder) {None=>{return;},Some(z)=>z}}
                    }
                    res.add_rule(f,args,alpha(alphabet,builder,queue,visited,zz,ty,Elimination));
                }
                f@ArbitraryFunc(w)=>{
                    let sf : Vec<usize> = args.iter().filter_map(|e|
                        if queue[*e].0.len()==1 {
                            if let Equal(Dsl::AccessStack(0),Exact(x)) = &queue[*e].0[0] {
                                Some(*x)
                            } else {None}
                        } else {None}
                    ).collect();
                    let rres = if sf.len()==args.len() {
                        vec![Equal(Dsl::AccessStack(0),Exact(builder.exec_function(w,args.iter().copied().collect())))]
                    } else {Vec::new()};
                    res.add_rule(f,args,alpha(alphabet,builder,queue,visited,rres,ty,Introduction));
                }
                _=>panic!()
            }
        }
        #[inline(always)]
        fn can_rule_out_constructor(
            builder:&ExpressionBuilder,
            preds:&Predlist,
            cstr:usize
        )->bool {
            // panic!("please refactor the constant matching into a property on skeleton.")
            if preds.len()>0 {
                if let Equal(Dsl::AccessStack(0),Exact(x)) = preds[0] {
                    match &builder.values[x].0 {
                        Const(f,_)=>{return *f != cstr;}
                        _=>panic!()
                    }
                }
                if let Equal(Dsl::AccessStack(0),Constsk(a,_)) = preds[0] {
                    if a != cstr {return true;}
                }
            }
            return false;
        }
        let mut res = PartialNFTA::new();
        res.add_rule(Input,Vec::new(),
            alpha(
                alphabet,builder,&mut queue,&mut visited,
                input,self.input_type,Elimination
            )
        );
        for nul in builder.get_nullary_constructors() {
            let rtype = builder.constructors[nul].restype;
            transfix(
                alphabet,builder,&mut queue,&mut visited,&mut res,
                Transition::Construct(nul),Vec::new(),rtype
            );
        }
        let mut gli = 0;
        while gli<queue.len() {
            let mut x = &queue[gli].0;
            let xt = queue[gli].1;
            let fresh = queue[gli].2;
            if let Elimination = fresh {
                match &builder.types[xt] {
                    EnumType(v)=>{
                        let v=v.clone();
                        for (w,cstr) in v.iter().zip(builder.get_constructors_for(xt)) {
                            for (i,yt) in w.iter().enumerate() {
                                transfix(
                                    alphabet,builder,&mut queue,&mut visited,&mut res,
                                    Destruct(cstr,i),vec![gli],*yt,
                                );
                                x = &queue[gli].0;
                            }
                        }
                    }
                    _=>{}
                }
            }
            if let Elimination = fresh {
                for oli in 0..gli {
                    let mut y = &queue[oli].0;
                    let yt = queue[oli].1;
                    let yfresh = queue[oli].2;
                    match &builder.types[xt] {
                        EnumType(v) if v.len()>1 =>{
                            let vl=v.len();
                            for (j,cstr) in builder.get_constructors_for(xt).into_iter().enumerate() {
                                if can_rule_out_constructor(builder,x,cstr) {continue;}
                                let mut nvm = vec![gli];
                                nvm.resize(1+vl,0);
                                nvm[j+1]=oli;
                                res.add_rule(Switch(vl),nvm,
                                    if let Introduction=yfresh {oli} else {
                                        let y=y.clone();
                                        alpha(
                                            alphabet,builder,&mut queue,&mut visited,
                                            y,yt,Introduction
                                        )
                                    }
                                );
                                x = &queue[gli].0;
                                y = &queue[oli].0;
                            }
                        }
                        _=>{}
                    }
                }
            }
            for oli in 0..gli {
                let mut y = &queue[oli].0;
                let yt = queue[oli].1;
                let yfresh = queue[oli].2;
                if let Elimination = yfresh {
                    match &builder.types[yt] {
                        EnumType(v) if v.len()>1 =>{
                            let vl=v.len();
                            for (j,cstr) in builder.get_constructors_for(yt).into_iter().enumerate() {
                                if can_rule_out_constructor(builder,y,cstr) {continue;}
                                let mut nvm = vec![oli];
                                nvm.resize(1+vl,0);
                                nvm[j+1]=gli;
                                res.add_rule(Switch(vl),nvm,
                                    if let Introduction=fresh {gli} else {
                                        let x=x.clone();
                                        alpha(
                                            alphabet,builder,&mut queue,&mut visited,
                                            x,xt,Introduction
                                        )
                                    }
                                );
                                x = &queue[gli].0;
                                y = &queue[oli].0;
                            }
                        }
                        _=>{}
                    }
                }
            }
            if xt==self.output_type {
                if output.moregeneral(x,builder) {
                    accepting_states.push(gli);
                }
            }
            processed_rel.entry(xt).or_default().push(gli);
            if let Some(z) = builder.stupid_typemap.get(&xt) {
                let z=z.clone();
                for (f_ind,s_ind) in z.iter() {
                    let (argtypes,restype) = match f_ind {
                        Function(x)=>{
                            let FunctionEntry {argtypes,restype,..} = &builder.functions[*x];
                            (argtypes,restype)
                        }
                        Constructor(x)=>{
                            let ConstructorEntry {argtypes,restype,..} = &builder.constructors[*x];
                            (argtypes,restype)
                        }
                    };
                    let restype=*restype;
                    let mut cartesian = vec![Vec::new()];
                    for (i,argtype) in argtypes.into_iter().enumerate() {
                        if i==*s_ind {
                            for c in cartesian.iter_mut() {c.push(gli);}
                            // println!("operated on cartesian {:?}",cartesian);
                            continue;
                        }
                        let mut swap_buf = Vec::new();
                        if let Some(v) = processed_rel.get(&argtype) {
                            for u in v.iter() {
                                for cart in cartesian.iter() {
                                    swap_buf.push({let mut cc=cart.clone();cc.push(*u);cc});
                                }
                            }
                        }
                        cartesian=swap_buf;
                        if cartesian.len()==0 {break;}
                    }
                    for cart in cartesian.into_iter() {
                        transfix(
                            alphabet,builder,&mut queue,&mut visited,&mut res,
                            match f_ind {
                                Constructor(x)=>Transition::Construct(*x),
                                Function(x)=>ArbitraryFunc(*x)
                            },cart,restype
                        );
                    }
                }
            }
            gli+=1;
        }
        // let StackElem {
        //     input,
        //     res,
        //     accepting_states,
        //     ..
        // } = stack.pop().unwrap();
        // graph_buffer.insert(input,res);
        // previous_accepting_states.insert(input,accepting_states);
        // }
        // let res = graph_buffer.remove(&input).unwrap();
        // println!("converting... {} states...",res.rules.len());
        res.convert(self,&accepting_states.iter().copied().collect(),interp,queue)
    }
}



// pub fn new_synthesize(
//     mut exprbuilder:ExpressionBuilder,
//     spec:SingleSpecDisjunct,
//     input_type:usize,
//     output_type:usize
// ) {
//     let mut nftabuilder = NFTABuilder::new(input_type,output_type);
//     let mut heap = BinaryHeap::new();
//     heap.push(QueueElem{ item:spec, priority:0 });
//     while let Some(QueueElem{ item:mut spec, .. }) = heap.pop() {
//         println!("popping!");
//         let mut order = spec.states.keys().copied().collect::<Vec<_>>();
//         order.sort_unstable_by_key(|x|exprbuilder.values[*x].1);

//         // let mut debug_converted = Vec::new();
//         // let mut debug_intersected = Vec::new();
//         for (interp,a) in order.into_iter().enumerate() {
//             println!("building nfta for: {:?}",DebugValue {
//                 t:a,
//                 expr:&exprbuilder
//             });
//             let newnfta = match nftabuilder.build_nfta(
//                 &mut exprbuilder,
//                 a,
//                 &confirmer,
//                 spec,
//                 &mut subex,
//                 100000,interp
//             ) {
//                 Some(z)=>z,
//                 _=>{
//                     //mark into omega
//                     println!("No accepting states after nfta built");
//                     continue 'specloop
//                 }
//             };
//             // debug_converted.push(newnfta);
//             spec.opnfta = match spec.opnfta {
//                 None=>Some(newnfta),
//                 Some(oldstate)=>{
//                     // println!("intersecting...");
//                     if let Some(intstate) = nftabuilder.intersect(newnfta,oldstate,None).and_then(|u|{nftabuilder.simplify(vec![u])})  {
//                         // debug_intersected.push(intstate);
//                         Some(intstate)
//                     } else {
//                         //mark into omega
//                         println!("No accepting states after intersection");
//                         continue 'specloop
//                     }
//                 }
//             };
//         }
//         println!("generating accepting run!");
//         let nfta = spec.opnfta.unwrap();
//         let accrunlist = nftabuilder.get_accepting_runs(nfta,&mut exprbuilder);
//         if accrunlist.len()==0 {
//             panic!("No accepting runs");
//             continue 'specloop
//         }

//         let mut yessides = (0..accrunlist.len()).map(|_|spec.clone()).collect::<Vec<_>>();
//         let mut noside = spec;
//         for ((solution,solsize,witness),mut yesspec) in accrunlist.into_iter().zip(yessides.into_iter()) {
//             println!("PARTIAL SOLUTION FOUND: {:#?}  {:?} {:?}",EnhancedPrintDsl{dsl:&solution,expr:&exprbuilder},witness,solsize);
//             let dslsol = Rc::new(solution.clone());
//             let tmemo = Rc::new(RefCell::new(HashMap::new()));
//             if states.iter().all(|(key,val)|{
//                 let relval = exprbuilder.eval_recursive_function(dslsol.clone(),tmemo.clone(),*key);
//                 // println!("f({:?}) = {:?}",DebugValue {
//                 //     t:*key,
//                 //     expr:&exprbuilder
//                 // },DebugValue {
//                 //     t:relval,
//                 //     expr:&exprbuilder
//                 // });
//                 relval != 0 && val.accepts(relval) && confirmer.accepts(&mut exprbuilder,*key,relval)
//             }) {
//                 println!("SOLUTION FOUND!");
//                 return;
//             }

//             println!("witness:");
//             for (k,v) in witness.iter() {
//                 println!("\tf({:?}) = {:?}",DebugValue {
//                     t:*k,
//                     expr:&exprbuilder
//                 },DebugValue {
//                     t:*v,
//                     expr:&exprbuilder
//                 });
//             }

//         }
//         return;
//         // let mut yes_side = spec.clone();
//         // let mut is_yes_ok = true;
//         // let disj : Vec<_> = witness.into_iter().map(|(k,v)|{
//         //     is_yes_ok = is_yes_ok && yes_side.refine(k,EqLit(v));
//         //     (k,NeqLit(v))
//         // }).collect();
//         // if is_yes_ok {
//         //     heap.push(QueueElem{ item:yes_side, priority:solsize });
//         // }
//         // if spec.refine_disjoint(disj) {
//         //     heap.push(QueueElem{ item:spec, priority:solsize });
//         // }
//         // break;
    
//     }
// }






