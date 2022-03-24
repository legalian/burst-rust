

use crate::cluster::{*};
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























