

use std::collections::HashMap;
use std::hash::Hash;
use std::mem::replace;

pub trait VerySimple : Hash+Copy+Eq+Default {}
impl<T:Hash+Copy+Eq+Default> VerySimple for T {}

pub struct GraphMutAB<'a,A:VerySimple,B:VerySimple,E,I:Iterator<Item=usize>> {
    alc:&'a mut [GraphBox<A,B,E>],
    i:I
}
impl<'a,E,A:VerySimple,B:VerySimple,I:Iterator<Item=usize>> Iterator for GraphMutAB<'a,A,B,E,I> {
    type Item = (&'a mut E,usize);
    fn next(&mut self) -> Option<Self::Item> {
        self.i.next().map(|x|{
            //here i fib to the type system because
            //i can garauntee that the same mutable pointer
            //won't be yielded twice, but the proof is non-trivial so
            //i can't prove it to the type system.
            println!("unsafe reached. -=-=-=-=-=-=-=-=-=-=-=-=-=-=- ");
            let GraphBox{e,..} = unsafe {
                &mut *self.alc.as_mut_ptr().add(x)
            };
            (e.as_mut().unwrap(),x)
        })
    }
}

pub struct GraphMutA<'a,A:VerySimple,B:VerySimple,E> {
    alc:&'a mut [GraphBox<A,B,E>],
    start:Option<usize>
}
impl<'a,A:VerySimple,B:VerySimple,E> Iterator for GraphMutA<'a,A,B,E> {
    type Item = (&'a mut E,usize,B);
    fn next(&mut self) -> Option<Self::Item> {
        self.start.map(|x|{
            println!("unsafe reached. -=-=-=-=-=-=-=-=-=-=-=-=-=-=- ");
            let GraphBox{e,right:n,b,..} = unsafe {
                &mut *self.alc.as_mut_ptr().add(x)
            };
            self.start=*n;
            (e.as_mut().unwrap(),x,*b)
        })
    }
}
pub struct GraphMutB<'a,A:VerySimple,B:VerySimple,E> {
    alc:&'a mut [GraphBox<A,B,E>],
    start:Option<usize>
}
impl<'a,A:VerySimple,B:VerySimple,E> Iterator for GraphMutB<'a,A,B,E> {
    type Item = (&'a mut E,usize,A);
    fn next(&mut self) -> Option<Self::Item> {
        self.start.map(|x|{
            println!("unsafe reached. -=-=-=-=-=-=-=-=-=-=-=-=-=-=- ");
            let GraphBox{e,down:n,a,..} = unsafe {
                &mut *self.alc.as_mut_ptr().add(x)
            };
            self.start=*n;
            (e.as_mut().unwrap(),x,*a)
        })
    }
}
pub struct GraphIterA<'a,A:VerySimple,B:VerySimple,E> {
    alc:&'a [GraphBox<A,B,E>],
    start:Option<usize>
}
impl<'a,A:VerySimple,B:VerySimple,E> Iterator for GraphIterA<'a,A,B,E> {
    type Item = (&'a E,usize,B);
    fn next(&mut self) -> Option<Self::Item> {
        self.start.map(|x|{
            let GraphBox{e,right:n,b,..} = &self.alc[x];
            self.start=*n;
            (e.as_ref().unwrap(),x,*b)
        })
    }
}
pub struct GraphIterB<'a,A:VerySimple,B:VerySimple,E> {
    alc:&'a [GraphBox<A,B,E>],
    start:Option<usize>
}
impl<'a,A:VerySimple,B:VerySimple,E> Iterator for GraphIterB<'a,A,B,E> {
    type Item = (&'a E,usize,A);
    fn next(&mut self) -> Option<Self::Item> {
        self.start.map(|x|{
            let GraphBox{e,down:n,a,..} = &self.alc[x];
            self.start=*n;
            (e.as_ref().unwrap(),x,*a)
        })
    }
}


pub struct GraphDestructAB<'a,A:VerySimple,B:VerySimple,E,I:Iterator<Item=usize>> {
    gr:&'a mut Graph<A,B,E>,
    i:I
}
impl<'a,A:VerySimple,B:VerySimple,E,I:Iterator<Item=usize>> Iterator for GraphDestructAB<'a,A,B,E,I> {
    type Item = (E,usize);
    fn next(&mut self) -> Option<Self::Item> {
        self.i.next().map(|x|(self.gr.remove_direct(x),x))
    }
}
impl<'a,A:VerySimple,B:VerySimple,E,I:Iterator<Item=usize>> Drop for GraphDestructAB<'a,A,B,E,I> {
    fn drop(&mut self) {
        self.for_each(drop)
    }
}

pub struct GraphDestructA<'a,A:VerySimple,B:VerySimple,E> {
    gr:&'a mut Graph<A,B,E>,
    start:Option<usize>
}
impl<'a,A:VerySimple,B:VerySimple,E> Iterator for GraphDestructA<'a,A,B,E> {
    type Item = (E,usize,B);
    fn next(&mut self) -> Option<Self::Item> {
        self.start.map(|x|{
            let GraphBox{e,right:n,b,..} = self.gr.remove_direct_with_links(x);
            self.start=n;
            (e.unwrap(),x,b)
        })
    }
}
impl<'a,A:VerySimple,B:VerySimple,E> Drop for GraphDestructA<'a,A,B,E> {
    fn drop(&mut self) {
        self.for_each(drop)
    }
}
pub struct GraphDestructB<'a,A:VerySimple,B:VerySimple,E> {
    gr:&'a mut Graph<A,B,E>,
    start:Option<usize>
}
impl<'a,A:VerySimple,B:VerySimple,E> Iterator for GraphDestructB<'a,A,B,E> {
    type Item = (E,usize,A);
    fn next(&mut self) -> Option<Self::Item> {
        self.start.map(|x|{
            let GraphBox{e,down:n,a,..} = self.gr.remove_direct_with_links(x);
            self.start=n;
            (e.unwrap(),x,a)
        })
    }
}
impl<'a,A:VerySimple,B:VerySimple,E> Drop for GraphDestructB<'a,A,B,E> {
    fn drop(&mut self) {
        self.for_each(drop)
    }
}


#[derive(Clone)]
pub struct GraphBox<A:VerySimple,B:VerySimple,E> {
    pub e:Option<E>,
    pub top:Option<usize>,
    pub left:Option<usize>,
    pub down:Option<usize>,
    pub right:Option<usize>,
    pub a:A,
    pub b:B
}
impl<A:VerySimple,B:VerySimple,E> Default for GraphBox<A,B,E> {
    fn default()->Self {
        GraphBox {
            e:None,top:None,left:None,down:None,right:None,
            a:Default::default(),
            b:Default::default()
        }
    }
}
#[derive(Clone)]
pub struct Graph<A:VerySimple,B:VerySimple,E> {
    allocator:Vec<GraphBox<A,B,E>>,//top left bottom right
    aside:HashMap<A,usize>,
    bside:HashMap<B,usize>,
    freefirst:Option<usize>,
    // direct:HashMap<(A,B),HashSet<usize>>
}

impl<A:VerySimple,B:VerySimple,E> Graph<A,B,E> {
    pub fn new() -> Graph<A,B,E> {
        Graph {
            allocator:Vec::new(),
            aside:HashMap::new(),
            bside:HashMap::new(),
            freefirst:None,
            // direct:HashMap::new()
        }
    }

    pub fn get_direct(&self,e:usize) -> &E {self.allocator[e].e.as_ref().unwrap()}
    pub fn get_direct_with_links(&self,e:usize) -> &GraphBox<A,B,E> {&self.allocator[e]}
    pub fn get_direct_mut(&mut self,e:usize) -> &mut E {self.allocator[e].e.as_mut().unwrap()}
    // pub fn get_direct_mut_with_links(&mut self,e:usize) -> &mut GraphBox<A,B,E> {&mut self.allocator[e]} this could be misused
    pub fn remove_direct(&mut self,e:usize) -> E {self.remove_direct_with_links(e).e.unwrap()}
    pub fn remove_direct_with_links(&mut self,e:usize) -> GraphBox<A,B,E> {
        let w@GraphBox{top:u,left:l,right:r,down:d,a,b,..} = replace(&mut self.allocator[e],GraphBox{top:self.freefirst,..Default::default()});
        self.freefirst = Some(e);
        match (u,d) {
            (None,None)=>{self.bside.remove(&b);}
            (None,Some(d))=>{self.bside.insert(b,d);}
            _=>{}
        }
        match (l,r) {
            (None,None)=>{self.aside.remove(&a);}
            (None,Some(r))=>{self.aside.insert(a,r);}
            _=>{}
        }
        if let Some(u)=u {self.allocator[u].down=d;}
        if let Some(l)=l {self.allocator[l].right=r;}
        if let Some(d)=d {self.allocator[d].top=u;}
        if let Some(r)=r {self.allocator[r].left=l;}
        w
    }
    // pub fn get(&self,a:A,b:B) -> impl Iterator<Item=(&E,usize)> {self.direct.get(&(a,b)).map(|v|v.iter().enumerate().map(|(i,x)|(self.allocator[*x].e.as_ref().unwrap(),i))).into_iter().flatten()}
    // pub fn get_mut(&mut self,a:A,b:B) -> impl Iterator<Item=(&mut E,usize)> {GraphMutAB{alc:&mut self.allocator,i:self.direct.get(&(a,b)).map(|x|x.iter().copied()).into_iter().flatten()}}
    // pub fn remove(&mut self,a:A,b:B) -> impl Iterator<Item=(E,usize)>+'_ {GraphDestructAB{i:self.direct.remove(&(a,b)).into_iter().map(|x|x.into_iter()).flatten(),gr:self}}
    pub fn iter_a(&self,a:A) -> impl Iterator<Item=(&E,usize,B)> {GraphIterA {alc:&self.allocator,start:self.aside.get(&a).copied()}}
    pub fn iter_b(&self,b:B) -> impl Iterator<Item=(&E,usize,A)> {GraphIterB {alc:&self.allocator,start:self.bside.get(&b).copied()}}
    pub fn iter_mut_a(&mut self,a:A) -> impl Iterator<Item=(&mut E,usize,B)> {GraphMutA {alc:&mut self.allocator,start:self.aside.get(&a).copied()}}
    pub fn iter_mut_b(&mut self,b:B) -> impl Iterator<Item=(&mut E,usize,A)> {GraphMutB {alc:&mut self.allocator,start:self.bside.get(&b).copied()}}
    pub fn remove_a(&mut self,a:A) -> impl Iterator<Item=(E,usize,B)>+'_ {GraphDestructA {start:self.aside.remove(&a),gr:self}}
    pub fn remove_b(&mut self,b:B) -> impl Iterator<Item=(E,usize,A)>+'_ {GraphDestructB {start:self.bside.remove(&b),gr:self}}
    pub fn first_a(&self,a:A) -> Option<usize> {self.aside.get(&a).copied()}
    pub fn first_b(&self,b:B) -> Option<usize> {self.bside.get(&b).copied()}
    pub fn direct_next_a(&self,d:usize) -> Option<usize> {self.allocator[d].right}
    pub fn direct_next_b(&self,d:usize) -> Option<usize> {self.allocator[d].down}

    pub fn preempt_spot(&mut self) -> usize {
        match self.freefirst {
            Some(a)=>a,
            None=>{
                self.allocator.push(GraphBox{top:self.freefirst,..Default::default()});
                self.freefirst = Some(self.allocator.len()-1);
                self.allocator.len()-1
            }
        }
    }
    pub fn insert(&mut self,a:A,b:B,e:E) -> usize {
        let gb = GraphBox{a,b,e:Some(e),
            top:self.bside.get(&b).copied(),
            left:self.aside.get(&a).copied(),
            down:None,right:None
        };
        let i = match self.freefirst {
            Some(a)=>{
                self.freefirst = self.allocator[a].top;
                self.allocator[a] = gb;
                a
            }
            None=>{
                self.allocator.push(gb);
                self.allocator.len()-1
            }
        };
        // self.direct.entry((a,b)).or_default().insert(i);
        self.aside.insert(a,i);
        self.bside.insert(b,i);
        i
    }
}

