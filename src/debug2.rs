

use crate::cluster::{*};
use crate::graph::{*};
use core::fmt::{Debug,Formatter,Error};



impl<T:Debug> Debug for Cluster<T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        let mut builder = f.debug_list();
        for (i,(a,_,_)) in self.cluster.iter().enumerate() {
            builder.entry(&(i,&a));
        }
        builder.finish()
    }
}


impl<A:VerySimple+Debug,B:VerySimple+Debug,E:Debug> Debug for Graph<A,B,E> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        let mut builder = f.debug_list();
        for (a,_) in self.aside.iter() {
            builder.entry(&(*a,self.iter_a(*a).collect::<Vec<_>>()));
        }
        builder.finish()
    }
}



























