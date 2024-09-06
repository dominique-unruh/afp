(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver54
imports "AutoCorres2.CTranslation"
begin

install_C_file "jiraver54.c"

context jiraver54_simpl
begin

thm f_body_def
thm f_modifies

end (* context *)


end
