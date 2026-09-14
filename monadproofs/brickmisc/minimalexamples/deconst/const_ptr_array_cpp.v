Set Default Goal Selector "!".

Require Import skylabs.lang.cpp.parser.

#[local] Open Scope pstring_scope.

#[local] Definition t1 : type := (Tptr (Qconst Tuchar)).
#[local] Definition t2 : type := (Tptr t1).
#[local] Definition n1 : name := (Nscoped (Nglobal (Nid "minimalexamples")) (Nfunction function_qualifiers.N "init_const_input_array" (t1 :: t2 :: nil))).

Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
cpp.prog source
  abi abi.abi_default
  defns
    (Dtypedef (Nglobal (Nid "__int128_t")) Tint128_t)
    (Dtypedef (Nglobal (Nid "__uint128_t")) Tuint128_t)
    (Dtypedef (Nglobal (Nid "__NSConstantString")) (Tnamed (Nglobal (Nid "__NSConstantString_tag"))))
    (Dtypedef (Nglobal (Nid "__builtin_ms_va_list")) (Tptr Tchar))
    (Dtypedef (Nglobal (Nid "__builtin_va_list")) (Tarray (Tnamed (Nglobal (Nid "__va_list_tag"))) 1))
    (Dtypedef (Nscoped (Nglobal (Nid "minimalexamples")) (Nid "byte")) Tuchar)
    (Dfunction n1
      (Build_Func Tvoid
        (("src", t1) :: ("dst", t2) :: nil) CC_C Ar_Definite exception_spec.MayThrow
        (Some (Impl
            (Sseq (
                (Sdecl (
                    (Dvar "inputs" (Tarray t1 1) None) :: nil)) ::
                (Sexpr
                  (Eassign
                    (Esubscript (Evar "inputs" (Tarray t1 1)) (Eint 0%Z Tint) t1)
                    (Ecast Cl2r (Evar "src" t1)) t1)) ::
                (Sexpr
                  (Eassign
                    (Ederef
                      (Ecast Cl2r (Evar "dst" t2)) t1)
                    (Ecast Cl2r
                      (Esubscript (Evar "inputs" (Tarray t1 1)) (Eint 0%Z Tint) t1)) t1)) :: nil)))))).
Notation module := source (only parsing).
