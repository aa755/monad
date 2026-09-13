Set Default Goal Selector "!".

Require Import skylabs.auto.cpp.proof.

Fixpoint isFunctionNamed2 (fname : ident) (n : name) : bool :=
  match n with
  | Nglobal (Nfunction _ i _) => bool_decide (i = fname)
  | Ninst nm _ => isFunctionNamed2 fname nm
  | Nscoped _ (Nfunction _ i _) => bool_decide (i = fname)
  | _ => false
  end.

Fixpoint containsDep (n : name) : bool :=
  match n with
  | Ndependent _ => true
  | Nglobal (Nfunction _ _ _) => false
  | Ninst nm _ => containsDep nm
  | Nscoped nm (Nfunction _ _ _) => containsDep nm
  | _ => false
  end.

Definition findBodyOfFnNamed2 (module : translation_unit) (filter : name → bool) : list (name * ObjValue):=
  List.filter (fun p => let '(nm, _) := p in filter nm) (NM.elements (symbols module)).

(* for newer version of cpp2v, change [tu_find.INFO.okind_of_value] in the defn below to [okind_of_value] *)
Definition lookupSymbolByFullName module (n : name) : option sym_info :=
  let el := NM.find n (symbols module) in
  option_map (fun x => {| info_name := n; info_type := fst (okind_of_value x) |}) el.

Definition firstEntryName (l : list (name * ObjValue)) :=
  List.nth 0 (map fst l) (Nunsupported "impossible").

Definition headName (l : list name) : name :=
  match l with
  | h :: _ => h
  | [] => "dipped()"%cpp_name
  end.

Definition functionNamed module s :=
  headName (rev (map fst (findBodyOfFnNamed2 module (isFunctionNamed2 s)))).

Definition lookup_function
           (tu : translation_unit) (nm : name)
  : option (sum Func Method) :=
  match symbols tu !! nm with
  | Some (Ofunction f) => Some (inl f)
  | Some (Omethod m)   => Some (inr m)
  | _                  => None
  end.




(* lookup a function/method declaration and its methods by fully‐qualified name *)
Definition symbol_table_to_list
  (st: skylabs.lang.cpp.syntax.translation_unit.symbol_table)
  : list (skylabs.lang.cpp.syntax.core.obj_name
          * skylabs.lang.cpp.syntax.translation_unit.ObjValue) :=
  (* NM.elements is already available and produces a list of (key * elt) *)
  skylabs.lang.cpp.syntax.namemap.NM.elements st.

#[only(lens)] derive Method'.

Definition AvailableButErased: option (OrDefault Stmt).
  exact None.
Qed.

Import LensNotations.
Open Scope lens_scope.
Definition erase_body (m:Method) : Method :=
  match m_body m with
  | Some (UserDefined _) =>  m &: _m_body .= AvailableButErased
  | _ => m
  end.

(* pick out a method of class [nm] from one symbol‐table entry *)
Definition select_method_of_class erase_body
           (nm: skylabs.lang.cpp.syntax.core.name)
           (entry: skylabs.lang.cpp.syntax.core.obj_name
                   * skylabs.lang.cpp.syntax.translation_unit.ObjValue)
  : option (skylabs.lang.cpp.syntax.core.obj_name
            * skylabs.lang.cpp.syntax.decl.Method) :=
  let '(n,o) := entry in
  match o with
  | skylabs.lang.cpp.syntax.translation_unit.Omethod m =>
      if bool_decide (skylabs.lang.cpp.syntax.decl.m_class m = nm)
      then Corelib.Init.Datatypes.Some (n, erase_body m)
      else Corelib.Init.Datatypes.None
  | _ => Corelib.Init.Datatypes.None
  end.



(* lookup the Struct declaration and its methods by fully‐qualified name *)
Definition lookup_struct' erase_body
           (tu: skylabs.lang.cpp.syntax.translation_unit.translation_unit)
           (nm: skylabs.lang.cpp.syntax.core.name)
  : option ( skylabs.lang.cpp.syntax.decl.Struct
             * list ( skylabs.lang.cpp.syntax.core.obj_name
                      * skylabs.lang.cpp.syntax.decl.Method ) ) :=
  match skylabs.lang.cpp.syntax.translation_unit.types tu !! nm with
  | Corelib.Init.Datatypes.Some (skylabs.lang.cpp.syntax.translation_unit.Gstruct st) =>
      let syms := skylabs.lang.cpp.syntax.translation_unit.symbols tu in
      let mds :=
        List.fold_right
          (fun entry acc =>
             match select_method_of_class erase_body nm entry with
             | Corelib.Init.Datatypes.Some md => md :: acc
             | Corelib.Init.Datatypes.None => acc
             end)
          []
          (symbol_table_to_list syms) in
      Corelib.Init.Datatypes.Some (st, mds)
  | _ =>
      Corelib.Init.Datatypes.None
  end.

Definition lookup_struct := lookup_struct' (fun x=>x).
Definition lookup_struct_short := lookup_struct' erase_body.
