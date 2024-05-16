(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

text \<open>
  In addition to named theorems, AutoCorres also stores definitions,
  theorems and other data in ML data structures.
  These can be useful for writing tools to process the AutoCorres output.

  See also: TraceDemo
\<close>
theory FunctionInfoDemo imports
  "AutoCorres2_Main.AutoCorres_Main"
begin


text \<open>Process a source file to populate our data structures.\<close>
install_C_file "function_info.c"
autocorres "function_info.c"
context function_info_all_corres begin

section \<open>Function info\<close>
text \<open>
  Information about all AutoCorres-processed functions is stored in the
  AutoCorresFunctionInfo structure.

  This structure stores information for all files that have been translated.
  It consists of three levels:

  1. Filename of the translation unit.
  2. Phase: the initial phase stores the C parser's output, and each
       subsequent translation phase that AutoCorres performs is recorded as well.
  3. Function: Each function that is processed in a given phase.
\<close>
ML \<open>
  val file_info: FunctionInfo.function_info Symtab.table FunctionInfo.Phasetab.table =
      the (Symtab.lookup (AutoCorresData.FunctionInfo.get (Context.Proof @{context})) "function_info")
\<close>

text \<open>
  The final stage is FunctionInfo.TS (type strengthening).
  This shows the final definition of each function in file_info:
\<close>
ML \<open>
  the (FunctionInfo.Phasetab.lookup file_info FunctionInfo.TS) |> Symtab.dest |> map snd
  |> app (fn f_info => writeln ("Definition of " ^ FunctionInfo.get_name f_info ^ ":\n" ^
                         Syntax.string_of_term @{context}
                           (Thm.prop_of (FunctionInfo.get_definition f_info))))
\<close>
text \<open>
  The function_info record also contains other data, such as function calls
  and intermediate correctness theorems.
  See the FunctionInfo structure for a full description.
\<close>

text \<open>
  We can also retrieve all intermediate phases.
  Besides being informative, these are also used by AutoCorres
  to resume partial translations; see Incremental.thy.
\<close>
ML \<open>
let
  val other_phases = [FunctionInfo.CP, FunctionInfo.L1, FunctionInfo.L2, FunctionInfo.HL, FunctionInfo.WA];
  fun get_def_at f phase =
        the (FunctionInfo.Phasetab.lookup file_info phase)
        |> (fn phase_info => FunctionInfo.get_definition (the (Symtab.lookup phase_info f)) );
in
  the (FunctionInfo.Phasetab.lookup file_info FunctionInfo.TS) |> Symtab.dest |> map fst
  |> app (fn f_name =>
       writeln ("Intermediate definitions of " ^ f_name ^ ":\n" ^
                String.concat (map (fn phase =>
                  Syntax.string_of_term @{context} (Thm.prop_of (get_def_at f_name phase)) ^ "\n")
                  other_phases)))
end
\<close>

text \<open>
  Note that the final @{term ac_corres} theorems are currently not stored
  in AutoCorresFunctionInfo; they are defined only as named theorems.
  (This is an oversight; there isn't any room in the current data structures
   for these theorems.)
\<close>
thm f'_ac_corres


section \<open>Heap info\<close>
text \<open>
  Information about the abstracted heap (if heap_abs is enabled) is also stored
  to the HeapInfo structure.
  See heap_lift_base.ML for which fields are contained in the structure.
\<close>
ML \<open>
  #heap_info (the (Symtab.lookup (HeapLiftBase.HeapInfo.get @{theory}) "function_info"))
\<close>

text \<open>
  HeapInfo also caches internal lemmas about the abstracted heap.
\<close>
ML \<open>
  #lifted_heap_lemmas (the (Symtab.lookup (HeapLiftBase.HeapInfo.get @{theory}) "function_info"))
\<close>

end
end
