section Parser
theory IpRoute_Parser
imports Routing_Table 
  IP_Addresses.IP_Address_Parser
keywords "parse_ip_route" "parse_ip_6_route" :: thy_decl
begin
text\<open>This helps to read the output of the \texttt{ip route} command into a @{typ "32 routing_rule list"}.\<close>

definition empty_rr_hlp :: "('a::len) prefix_match \<Rightarrow> 'a routing_rule" where
  "empty_rr_hlp pm = routing_rule.make pm default_metric (routing_action.make '''' None)"

lemma empty_rr_hlp_alt:
  "empty_rr_hlp pm = \<lparr> routing_match = pm, metric = 0, routing_action = \<lparr>output_iface = [], next_hop = None\<rparr>\<rparr>"
  unfolding empty_rr_hlp_def routing_rule.defs default_metric_def routing_action.defs ..

definition routing_action_next_hop_update :: "'a word \<Rightarrow> 'a routing_rule \<Rightarrow> ('a::len) routing_rule"
  where
  "routing_action_next_hop_update h pk = pk\<lparr> routing_action := (routing_action pk)\<lparr> next_hop := Some h\<rparr> \<rparr>"
lemma "routing_action_next_hop_update h pk = routing_action_update (next_hop_update (\<lambda>_. (Some h))) (pk::32 routing_rule)"
  by(simp add: routing_action_next_hop_update_def)

definition routing_action_oiface_update :: "string \<Rightarrow> 'a routing_rule \<Rightarrow> ('a::len) routing_rule"
  where
  "routing_action_oiface_update h pk = routing_action_update (output_iface_update (\<lambda>_. h)) (pk::'a routing_rule)"
lemma "routing_action_oiface_update h pk = pk\<lparr> routing_action := (routing_action pk)\<lparr> output_iface :=  h\<rparr> \<rparr>"
  by(simp add: routing_action_oiface_update_def)

(* Could be moved to Bitmagic *)
definition "default_prefix = PrefixMatch 0 0"
lemma default_prefix_matchall: "prefix_match_semantics default_prefix ip"
  unfolding default_prefix_def by (simp add: valid_prefix_00 zero_prefix_match_all)

definition "sanity_ip_route (r::('a::len) prefix_routing) \<equiv> correct_routing r \<and> unambiguous_routing r \<and> list_all ((\<noteq>) '''' \<circ> routing_oiface) r"
text\<open>The parser ensures that @{const sanity_ip_route} holds for any ruleset that is imported.\<close>

(* Hide all the ugly ml in a file with the right extension *)
(*Depends on the function parser_ipv4 from IP_Address_Parser*)
ML_file \<open>IpRoute_Parser.ml\<close>
                  
ML\<open>
  Outer_Syntax.local_theory @{command_keyword parse_ip_route}
  "Load a file generated by ip route and make the routing table definition available as isabelle term"
  (Parse.binding --| @{keyword "="} -- Parse.string >> register_ip_route 32)
\<close>

ML\<open>
  Outer_Syntax.local_theory @{command_keyword parse_ip_6_route}
  "Load a file generated by ip -6 route and make the routing table definition available as isabelle term"
  (Parse.binding --| @{keyword "="} -- Parse.string >> register_ip_route 128)
\<close>

parse_ip_route "rtbl_parser_test1" = "ip-route-ex"
lemma  "sanity_ip_route rtbl_parser_test1" by eval (* checked by parse_ip_route alread *)

lemma "rtbl_parser_test1 =
  [\<lparr>routing_match = PrefixMatch 0xFFFFFF00 32, metric = 0, routing_action = \<lparr>output_iface = ''tun0'', next_hop = None\<rparr>\<rparr>,
  \<lparr>routing_match = PrefixMatch 0xA0D2AA0 28, metric = 303, routing_action = \<lparr>output_iface = ''ewlan'', next_hop = None\<rparr>\<rparr>,
  \<lparr>routing_match = PrefixMatch 0xA0D2500 24, metric = 0, routing_action = \<lparr>output_iface = ''tun0'', next_hop = Some 0xFFFFFF00\<rparr>\<rparr>,
  \<lparr>routing_match = PrefixMatch 0xA0D2C00 24, metric = 0, routing_action = \<lparr>output_iface = ''tun0'', next_hop = Some 0xFFFFFF00\<rparr>\<rparr>,
  \<lparr>routing_match = PrefixMatch 0 0, metric = 303, routing_action = \<lparr>output_iface = ''ewlan'', next_hop = Some 0xA0D2AA1\<rparr>\<rparr>]"
by eval

parse_ip_6_route "rtbl_parser_test2" = "ip-6-route-ex"
value[code] rtbl_parser_test2
lemma  "sanity_ip_route rtbl_parser_test2" by eval

end