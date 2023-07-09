(*
 * This is an autogenerated file. Do not edit.
 * It was created using instantiate_laws.py.
 * It checks whether the other autogenerated files are up-to-date.
 *)

theory Check_Autogenerated_Files
  (* These imports are not actually needed, but in jEdit, they will conveniently trigger a re-execution of the checking code below upon changes. *)
  imports Laws_Classical Laws_Quantum Laws_Complement_Quantum
begin

ML \<open>
let
  fun check kind file expected = let
    val content = File.read (Path.append (Resources.master_directory \<^theory>) (Path.basic file))
    val hash = SHA1.digest content |> SHA1.rep
    in
      if hash = expected then () else
      error (kind ^ " file " ^ file ^ " has changed.\nPlease run \"python3 instantiate_laws.py\" to recreated autogenerated files.\nExpected SHA1 hash " ^ expected ^ ", got " ^ hash)
    end
in
  check "Source" "Axioms_Classical.thy" "22b277e3a4e6b4a8da06cbb18a17b627899617e0";
  check "Source" "Axioms_Quantum.thy" "1b8699db8ae648b78f8a5dfc272daa2e11ff2f95";
  check "Source" "Laws.thy" "2ee411308f3af61f02be644f0ad2d59a9fcbc45b";
  check "Source" "Laws_Complement.thy" "f45df84a60a619b391958d029feb09bbfaea467a";
  check "Generated" "Laws_Classical.thy" "8a3867acda9a82776278c6366f8950f3d988b189";
  check "Generated" "Laws_Complement_Quantum.thy" "fee565455d1dfa024751ffa2c9a381663787fb5b";
  check "Generated" "Laws_Quantum.thy" "cb971fd2223e5ecd8ae8caaa50237b7405e36c2a"
end
\<close>

end
