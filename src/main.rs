

#![allow(dead_code)]
mod mlsparser;
mod ntfa;
mod nftabuilder;
mod cluster;
mod graph;
mod queue;
mod spec;
mod dsl;
mod debug;
mod synthesis;

use std::ffi::OsStr;
use std::fs::read_dir;
use dsl::interpret_file;
use synthesis::synthesize;
use std::path::PathBuf;
use std::time::{Instant};



fn main() {
    println!("just because you found a solution doesn't mean that it's the smallest solution of that branch.");
    println!("you'll need to further refine your answer before you output it.");
    println!("");
    println!("");
    println!("");
    println!("");
    println!("");
    println!("ought to release unused placeholders back into the pool with a cluster data structure.");
    println!("");
    println!("");
    println!("");
    println!("");
    println!("simplify singular alim, blim");
    println!("");
    println!("issue: replace hashset with BTreeSet anytime you need iteration; hashset is terrible at it.");
    println!("");
    println!("");
    println!("");
    println!("");
    println!("");
    println!("so maybe the reason it's going wrong is that (&[],&[]) doesn't work because there are weird duplicate interactions.");

    println!("");
    println!("");
    println!("constants may be important");
    println!("simplifying inplace to skip work on singular pools may be important");
    println!("");
    println!("");

    let mut paths : Vec<PathBuf> = read_dir("evaluation/benchmarks/io").unwrap().into_iter().chain(
        read_dir("evaluation/benchmarks/logical").unwrap().into_iter()).chain(
            read_dir("evaluation/benchmarks/ref").unwrap().into_iter()).filter_map(|x|{
                let p = x.unwrap().path();
                if p.extension().and_then(OsStr::to_str)==Some("decls") {None}
                else {Some(p)}
            }).collect();
    paths.sort();
    for fullpath in paths.into_iter().skip(7).take(1) {
        println!("");
        let (builder,spec,(input_type,output_type)) = interpret_file(fullpath);
        let now = Instant::now();
        synthesize(builder,spec,input_type,output_type);
        println!("time taken: {}/1000 seconds", now.elapsed().as_millis());
    }
    // for fullpath in paths.into_iter().skip(7).take(1) {
    //     let (builder,spec,(input_type,output_type)) = interpret_file(fullpath);
    //     synthesize(builder,spec,input_type,output_type);
    // }
}







