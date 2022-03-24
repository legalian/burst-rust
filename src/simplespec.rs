


// use std::collections::HashMap;
// use std::collections::HashSet;
// use std::collections::hash_map::Entry::*;

// use crate::nftabuilder::{*};
// use crate::nfta::{*};
// use ProcValue::{*};


// #[derive(Clone,Debug)]
// pub struct SimpleSpecElem {
//     pub graph_buffer : PartialNFTA,
//     pub accepting_states : HashSet<(usize,TermClassification)>,
//     pub term_size_limiter : usize,
//     pub state : usize
// }
// #[derive(Clone,Debug)]
// pub struct SimpleSpecDisjunct {
//     pub opnfta : Option<usize>,
//     pub states : HashMap<usize,SimpleSpecElem>
// }
// impl SimpleSpecDisjunct {
//     pub fn refine(&mut self,a:usize,lit:usize)->bool {
//         self.opnfta = None;
//         match self.states.entry(a) {
//             Occupied(mut x)=>{
//                 let x = x.get_mut();
//                 println!("you could do a better job intersecting with wildcards...");
//                 if !x.state != lit {return false}
//             }
//             Vacant(x)=>{x.insert(SimpleSpecElem {
//                 graph_buffer : PartialNFTA::new(),
//                 accepting_states : HashSet::new(),
//                 term_size_limiter : 2,
//                 state : lit
//             });}
//         }
//         for (_,v) in self.states.iter_mut() {
//             v.graph_buffer.refine(a,lit);
//         }
//         true
//     }
// }


