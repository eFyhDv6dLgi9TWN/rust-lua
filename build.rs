use std::{
    env::{self, current_dir},
    path::PathBuf,
};

fn main() {
    let config = pkg_config::Config::new();

    let library = config
        .probe("luajit")
        .expect("pkg_config::Config::probe failed");

    let bindings = bindgen::builder()
        // Header.
        .header_contents(
            "wrapper.h",
            r#"#include <lua.h>
               #include <lauxlib.h>"#,
        )
        // Include directory.
        .clang_args(library.include_paths.iter().map(|p| {
            let mut include_path = "-I".to_owned();
            include_path.push_str(p.to_str().unwrap());
            include_path
        }))
        // size_t.
        .size_t_is_usize(true)
        // Macro type.
        .default_macro_constant_type(bindgen::MacroTypeVariation::Signed)
        // Blocklist.
        .blocklist_function("lua_pushcclosure")
        // Tests.
        .layout_tests(false)
        // rustfmt.
        .rustfmt_bindings(true)
        .rustfmt_configuration_file(Some(
            current_dir()
                .expect("current_dir failed")
                .join("rustfmt.toml"),
        ))
        // Generate bindings.
        .generate()
        .expect("bindgen::Builder::generate failed");

    let out_path = PathBuf::from(
        env::var("OUT_DIR").expect("env::var(\"OUTDIR\") failed"),
    );

    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("bindgen::Bindings::write_to_file failed")
}
