use modules::exec;

macro_rules! assert_exec {
    ($s:expr) => {{
        let r = exec($s.chars());
        assert!(r.is_ok(), "{:?}", r.unwrap_err());
    }};
}

#[test]
fn test_execution() {
    assert_exec!("struct end");
    assert_exec!("struct val x = 1 end");

    assert_exec!(
        "struct
         val x = 1
         val y = 1
         end"
    );

    assert_exec!(
        "struct
           module M = struct end

           module W = struct
             val x = 1
           end
         end"
    );
}
