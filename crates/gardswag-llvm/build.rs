fn main() {
    // TODO: get these infos from llvm-config, maybe??
    println!("cargo:rustc-link-lib=LLVM-14");

    cxx_build::bridge("src/lib.rs")
        .file("src/gdsllvm.cxx")
        .flag_if_supported("-std=c++17")
        .compile("gdsllvm");
}
