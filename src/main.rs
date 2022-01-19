

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


fn main() {
    println!("your stack impl where you build all the starting points won't work");
    println!("just because you found a solution doesn't mean that it's the smallest solution of that branch.");
    println!("you'll need to further refine your answer before you output it.");
    // println!("")

    let mut paths : Vec<PathBuf> = read_dir("evaluation/benchmarks/io").unwrap().into_iter().chain(
        read_dir("evaluation/benchmarks/logical").unwrap().into_iter()).chain(
            read_dir("evaluation/benchmarks/ref").unwrap().into_iter()).filter_map(|x|{
                let p = x.unwrap().path();
                if p.extension().and_then(OsStr::to_str)==Some("decls") {None}
                else {Some(p)}
            }).collect();
    paths.sort();
    // for fullpath in paths.into_iter().skip(5).take(1) {
    //     let (builder,spec,(input_type,output_type)) = interpret_file(fullpath);
    //     synthesize(builder,spec,input_type,output_type);
    // }
    for fullpath in paths.into_iter().take(1) {
        let (builder,spec,(input_type,output_type)) = interpret_file(fullpath);
        synthesize(builder,spec,input_type,output_type);
    }
    // for fullpath in paths.into_iter().skip(7).take(1) {
    //     let (builder,spec,(input_type,output_type)) = interpret_file(fullpath);
    //     synthesize(builder,spec,input_type,output_type);
    // }
}







