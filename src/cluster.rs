

use std::mem::replace;

#[derive(Clone)]
pub struct Cluster<T> {
    cluster:Vec<(Option<T>,Option<usize>,Option<usize>)>,
    first:Option<usize>,
    last:Option<usize>,
    freefirst:Option<usize>,
    count:usize
}


pub struct ClusterIter<'a,T> {
    cl:&'a Cluster<T>,
    i:Option<usize>
}
impl<T> Cluster<T> {
    pub fn iter(&self) -> ClusterIter<T> {
        ClusterIter {i:self.first,cl:self}
    }
    pub fn iter_from(&self,i:Option<usize>) -> ClusterIter<T> {
        ClusterIter {i,cl:self}
    }
}
impl<'a,T> Iterator for ClusterIter<'a,T> {
    type Item = (&'a T,usize);
    fn next(&mut self) -> Option<Self::Item> {
        self.i.map(|x|{
            let (t,_,r) = &self.cl.cluster[x];
            self.i=r.clone();
            (t.as_ref().unwrap(),x)
        })
    }
}
impl<'a,T> IntoIterator for &'a Cluster<T> {
    type Item = (&'a T,usize);
    type IntoIter = ClusterIter<'a,T>;
    fn into_iter(self) -> Self::IntoIter {self.iter()}
}




pub struct ClusterIterMut<'a,T> {
    cl:&'a mut Cluster<T>,
    i:Option<usize>
}
impl<T> Cluster<T> {
    pub fn iter_mut(&mut self) -> ClusterIterMut<T> {
        ClusterIterMut {i:self.first,cl:self}
    }
    pub fn iter_mut_from(&mut self,i:Option<usize>) -> ClusterIterMut<T> {
        ClusterIterMut {i,cl:self}
    }
}
impl<'a,T> Iterator for ClusterIterMut<'a,T> {
    type Item = (&'a mut T,usize);
    fn next(&mut self) -> Option<Self::Item> {
        self.i.map(|x|{
            let (t,_,r) = unsafe {
                &mut *self.cl.cluster.as_mut_ptr().add(x)
            };
            self.i=r.clone();
            (t.as_mut().unwrap(),x)
        })
    }
}
impl<'a,T> IntoIterator for &'a mut Cluster<T> {
    type Item = (&'a mut T,usize);
    type IntoIter = ClusterIterMut<'a,T>;
    fn into_iter(self) -> Self::IntoIter {self.iter_mut()}
}



pub struct ClusterIntoIter<T> {
    cluster:Vec<(Option<T>,Option<usize>,Option<usize>)>,
    first:Option<usize>
}
impl<T> Iterator for ClusterIntoIter<T> {
    type Item = (T,usize);
    fn next(&mut self) -> Option<Self::Item> {
        self.first.map(|x|{
            let (t,_,r) = replace(&mut self.cluster[x],(None,None,None));
            self.first = r;
            (t.unwrap(),x)
        })
    }
}
impl<T> IntoIterator for Cluster<T> {
    type Item = (T,usize);
    type IntoIter = ClusterIntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        ClusterIntoIter {
            cluster:self.cluster,
            first:self.first
        }
    }
}

impl<T> FromIterator<T> for Cluster<T> {
    fn from_iter<I>(iter: I) -> Self where I: IntoIterator<Item = T> {
        let mut clus : Vec<_> = iter.into_iter().enumerate().map(|(i,x)|(
            Some(x),
            if i==0 {None} else {Some(i-1)},
            Some(i+1)
        )).collect();
        let clen = clus.len();
        if clen==0 {return Cluster::new();}
        clus[clen-1].2=None;
        Cluster {
            cluster:clus,
            freefirst:None,
            first:Some(0),
            last:Some(clen-1),
            count:clen
        }
    }
}
impl<T> Cluster<T> {
    pub fn new() -> Cluster<T> {
        Cluster {
            cluster:Vec::new(),
            freefirst:None,
            first:None,
            last:None,
            count:0
        }
    }
    pub fn first(&self) -> Option<usize> {self.first}
    pub fn last(&self) -> Option<usize> {self.last}
    pub fn next(&self,i:usize) -> Option<usize> {self.cluster[i].2}
    pub fn prev(&self,i:usize) -> Option<usize> {self.cluster[i].1}
    pub fn len(&self) -> usize {self.count}
    pub fn preempt_spot(&mut self) -> usize {
        match self.freefirst {
            Some(a)=>a,
            None=>{
                self.cluster.push((None,None,self.freefirst));
                self.freefirst=Some(self.cluster.len()-1);
                self.cluster.len()-1
            }
        }
    }
    pub fn get(&self,i:usize) -> &T {self.cluster[i].0.as_ref().unwrap()}
    pub fn get_mut(&mut self,i:usize) -> &mut T {self.cluster[i].0.as_mut().unwrap()}
    pub fn remove(&mut self,i:usize) -> T {
        self.count-=1;
        let (t,l,r) = replace(&mut self.cluster[i],(None,None,self.freefirst));
        match l {
            Some(l)=>{self.cluster[l].2=r;}
            None=>{self.first=r;}
        }
        match r {
            Some(r)=>{self.cluster[r].1=l;}
            None=>{self.last=l;}
        }
        t.unwrap()
    }
    pub fn insert(&mut self,t:T) -> usize {
        self.count+=1;
        match self.freefirst {
            Some(a)=>{
                if let Some(b) = self.first {
                    self.cluster[b].1=Some(a);
                }
                self.freefirst = self.cluster[a].2;
                self.cluster[a] = (Some(t),None,self.first);
                self.first=Some(a);
                a
            }
            None=>{
                if let Some(b) = self.first {
                    self.cluster[b].1=Some(self.cluster.len());
                }
                self.cluster.push((Some(t),None,self.first));
                self.first=Some(self.cluster.len()-1);
                self.last=Some(self.cluster.len()-1);
                self.cluster.len()-1
            }
        }
    }
}

