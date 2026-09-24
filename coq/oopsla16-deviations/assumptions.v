(** Prints the assumptions of every result in this directory.  Each line of
    output should read "Closed under the global context". *)
Require Import dot_spec regularity ctx_restriction store_restriction.

Print Assumptions all_closed.
Print Assumptions htp_closed_Sx.
Print Assumptions restriction_harmless.
Print Assumptions restriction_harmless_empty.
Print Assumptions ctx_restriction_is_real.
Print Assumptions bad_stores_not_ok.
Print Assumptions typed_over_top_member.
Print Assumptions store_restriction_is_real.
