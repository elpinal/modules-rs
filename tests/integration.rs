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

    assert_exec!(
        "struct
           val a = 1
           val b = 1
           val c = 1
         end"
    );

    assert_exec!(
        "struct
           val x = 20

           module W = struct
             val y = 40
             val f = λa.a
           end
         end"
    );

    assert_exec!(
        "struct
           module M = fun X : sig end =>
             ( struct
               module M = struct type t = int end
             end
             ).M

           module E = struct end

           type t = (M E).t
           type s = (M E).t

           module W = struct
             val x = λa.a
             val f = λa.a
           end
         end"
    );
}
