theory op_tee_init
imports "Op_Tee_Def" "Op_Tee_Spec" "../State_Machine"

begin

section"The sys instantiation of state machine"

consts sys_conf :: "Sys_Conf"

definition sys_config_witness :: "Sys_Conf"
  where "sys_config_witness \<equiv> 
  \<lparr> kerneler_conf = undefined,
    cpus_conf={},
    procs_conf =Map.empty,
    objs_conf = Map.empty \<rparr>"

specification(sys_conf)
  proc_not_kernel: "(procs_conf sys_conf) x \<noteq> None 
                    \<Longrightarrow> x \<noteq> kerneler_conf sys_conf"
  kernel_not_proc: "kerneler_conf sys_conf = x 
                    \<Longrightarrow> (procs_conf sys_conf) x = None"
  domainid_eq_pid: "\<forall> p. (procs_conf sys_conf) p \<noteq> None 
                    \<longrightarrow> subjid_name(subjattr_procid(proc_subattr_conf(the((procs_conf sys_conf) p))))  = p"
proof-
  have p1: "\<exists> f n na .f (n::nat) = (None::Proc_Conf option) \<and> f na = None \<and> na \<noteq> n"
    by fastforce
  have p2: "\<exists> sys_conf .(\<forall> p. (procs_conf sys_conf) p \<noteq> None 
                    \<longrightarrow> subjid_name(subjattr_procid(proc_subattr_conf(the((procs_conf sys_conf) p))))  = p)"
    using sys_config_witness_def
    by (metis Sys_Conf.select_convs(3))
  show ?thesis
    using sys_config_witness_def p1 p2
  proof -
    show ?thesis
      by (metis Sys_Conf.select_convs(1) Sys_Conf.select_convs(3) sys_config_witness_def)
  qed   
qed

definition sys_init :: "Sys_Conf \<Rightarrow> Sys_State"
  where"sys_init sc \<equiv> \<lparr> 
                        currents = Map.empty,                      
                        objs = Map.empty,
                        procs = Map.empty,
                        memories = {},
                        mode = (TEE Privilege)
                       \<rparr>"

consts fn_s0 :: Sys_State

definition "fn_s0_witness \<equiv> sys_init sys_conf"

specification(fn_s0)
  fn_s0_init: "fn_s0 = fn_s0_witness"
  by simp

definition fn_step :: "Event \<Rightarrow> (Sys_State\<times> Sys_State) set"
  where"fn_step event = {(s,s'). s' \<in> 
  (case 
    event 
   of 
    sys_call (TEE_OBJ_CREATE sc poa) pa \<Rightarrow>
                            {fst(utee_obj_create s sc pa poa)} |
    sys_call (TEE_OBJ_COPY poa r) pa \<Rightarrow>
                            {fst(utee_obj_copy s pa poa r)} |
    sys_call (TEE_OBJ_CLOSE poa) pa \<Rightarrow>
                            {fst(utee_obj_close s pa poa)} |
    sys_call (TEE_OBJ_DEL poa) pa \<Rightarrow>
                            {fst(utee_obj_del s pa poa)} |
    sys_call (TEE_OBJ_TRANS dst_pa channel_poa trans_poa) src_pa \<Rightarrow>
                            {fst(utee_channel_transmit s src_pa dst_pa channel_poa trans_poa)}|
    kernel_event (TEE_OBJ_DEBUG poa) pa \<Rightarrow>
                            {fst(mbedtls_debug_print_buf s pa poa)})}"

(*get the domain*)
definition fn_dom :: "Sys_State \<Rightarrow> Event \<Rightarrow> Pid option"
  where "fn_dom s e \<equiv>
  case 
    e
  of
    sys_call _ poa \<Rightarrow> Some(subjid_name(subjattr_procid(poa)))"

definition equiv_object :: "Sys_State \<Rightarrow> Kid \<Rightarrow> Sys_State \<Rightarrow> bool"
  where "equiv_object s kid t \<equiv>
  kernel_objs s kid = kernel_objs t kid"

definition equiv_handle:: "Sys_State \<Rightarrow> Pid \<Rightarrow> Sys_State \<Rightarrow> bool"
  where "equiv_handle s pid t \<equiv>
  \<forall> hid . proc_handles(the(procs s pid)) hid = proc_handles(the(procs t pid)) hid \<and>
          equiv_object s (kernel_obj_id(the(proc_handles(the(procs s pid)) hid))) t"

definition equiv_proc :: "Sys_State \<Rightarrow> Pid \<Rightarrow> Sys_State \<Rightarrow> bool"
  where "equiv_proc s pid t \<equiv>
  procs s pid = procs t pid \<and> equiv_handle s pid t"

definition fn_equiv :: "Sys_State \<Rightarrow> Pid \<Rightarrow> Sys_State \<Rightarrow> bool" ("(_~_~_)")
  where "fn_equiv s pid t \<equiv>
  if
    is_proc sys_conf pid
  then
    equiv_proc s pid t
  else if 
    is_kernel sys_conf pid
  then
    True
  else
    False"


definition fn_interfence :: "Pid \<Rightarrow> Pid \<Rightarrow> bool" ("(_ \<leadsto> _)")
  where "fn_interfence d1 d2 \<equiv>
  if
    d1 = d2
  then
    True
  else if
    is_kernel sys_conf d1
  then
    True
  else
    False"

definition fn_non_interference :: "Pid \<Rightarrow> Pid \<Rightarrow> bool" ("(_ \<setminus>\<leadsto> _)")
  where "(u \<setminus>\<leadsto>  v) \<equiv> \<not> (u \<leadsto> v)"

declare equiv_object_def[cong] and equiv_handle_def[cong] and equiv_proc_def[cong] and
        fn_equiv_def[cong] fn_interfence_def[cong] fn_non_interference_def[cong] and fn_dom_def[cong]

lemma equiv_proc_transitive :
  "\<forall> s t r d. equiv_proc s d t \<and> equiv_proc t d r 
              \<longrightarrow> equiv_proc s d r"
   by auto

lemma equiv_proc_symmetic :
  "\<forall> s t d. equiv_proc s d t 
            \<longrightarrow> equiv_proc t d s"
  by auto

lemma equiv_proc_reflexive : 
  "\<forall> s d. equiv_proc s d s"
  by auto

lemma fn_equiv_relfexive:
  "\<forall> s d . fn_equiv s d s"
  using equiv_proc_reflexive try0 
lemma fn_kernel_intf_all :
  "\<forall> d. fn_interfence (kerneler_conf sys_conf) d"
  by (simp add: is_kernel_def)

lemma fn_not_intf_kernel :
  "\<forall> d. fn_interfence d (kerneler_conf sys_conf) \<longrightarrow>
        d = (kerneler_conf sys_conf)"
  by (simp add: is_kernel_def)

lemma fn_intf_reflexive: "fn_interfence d d"
  by auto

lemma fn_reachable: 
  "\<forall> s a. (SM.reachable0 fn_s0 fn_step) s \<longrightarrow>
          (\<exists> s'. (s,s') \<in> fn_step a)"
proof -
  {
    fix s a
    assume p0: "(SM.reachable0 fn_s0 fn_step) s"
    have "\<exists> s' .(s,s') \<in> fn_step a"
    proof(induct a)
      case (sys_call x1 x2)
      then show ?case
        apply(induct x1)
        by (simp add:fn_step_def)+
    next
      case (kernel_event x1 x2)
      then show ?case 
        apply (induct x1)
      by (simp add:fn_step_def)+
    qed
  }
  then show ?thesis by simp
qed

interpretation SM_enabled
        fn_s0 fn_step fn_dom  "kerneler_conf sys_conf" fn_equiv fn_interfence
  using fn_reachable fn_kernel_intf_all fn_not_intf_kernel equiv_proc_reflexive
        equiv_proc_transitive equiv_proc_symmetic fn_intf_reflexive
end