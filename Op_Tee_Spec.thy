theory Op_Tee_Spec
imports Main "Op_Tee_Def"

begin
section "define interfaces of op-tee"
section "Basic definition"
definition get_pa_id :: "SubjAttribute \<Rightarrow> Pid"
  where "get_pa_id pa \<equiv>
  subjid_name(subjattr_procid(pa))"

definition is_proc_exist :: "Sys_State \<Rightarrow> SubjAttribute \<Rightarrow> bool"
  where "is_proc_exist s pa \<equiv>
  procs s (get_pa_id pa) \<noteq> None \<and>
  (proc_attr(the(procs s (get_pa_id pa))) = pa)"

definition is_kernel_obj_conf_exist :: "Sys_Conf \<Rightarrow> Kid \<Rightarrow> bool"
  where "is_kernel_obj_conf_exist sc kid \<equiv>
  kernel_objs_conf sc kid \<noteq> None"

definition get_poa_id :: "PobjAttribute \<Rightarrow> Kid"
  where "get_poa_id poa \<equiv>
  resrcid_name(pobjattr_objid poa)"

definition is_kernel_obj_exist :: "Sys_State \<Rightarrow> PobjAttribute \<Rightarrow> bool"
  where "is_kernel_obj_exist s poa \<equiv>
  procs s (get_poa_id poa)\<noteq> None \<and> 
  obj_attr(the(kernel_objs s (get_poa_id poa))) = poa"

definition get_pa_uid :: "SubjAttribute \<Rightarrow> nat"
  where "get_pa_uid pa \<equiv>
  roleid_name(subjattr_callerid pa)"

definition is_uid_in_poa :: "SubjAttribute \<Rightarrow> PobjAttribute \<Rightarrow> bool"
  where "is_uid_in_poa sa poa \<equiv>
  get_pa_uid sa = roleid_name(pobjattr_usrid poa)"

definition proc_right_check :: "Sys_State \<Rightarrow> Right \<Rightarrow> Pid \<Rightarrow> bool"
  where "proc_right_check s r pid \<equiv>
  if
    (procs s pid) \<noteq> None  
  then 
    let
      proc = the(procs s pid);
      right_set = proc_rights(proc)
    in
      r \<in> right_set
  else
    False"

definition is_addr_conflicted :: "Addr \<Rightarrow> Addr \<Rightarrow> bool"
  where "is_addr_conflicted x y \<equiv> 
  start(x) < (size(y)+start(y)) \<and> 
  start(y) < (start(x)+size(x))"

definition is_memories_conflicted:: "Sys_State \<Rightarrow> Addr \<Rightarrow> bool"
  where "is_memories_conflicted s y \<equiv> 
  \<exists> x .x\<in> memories(s) \<and> is_addr_conflicted x y"

definition get_kernel_obj_from_config :: "Sys_Conf \<Rightarrow> Kid \<Rightarrow> Kernel_Obj_Conf"
  where "get_kernel_obj_from_config sc kid \<equiv>
  the(kernel_objs_conf(sc) kid)"

definition create_kernel_obj :: "Sys_State \<Rightarrow> PobjAttribute \<Rightarrow> InfoAttribute \<Rightarrow> Addr \<Rightarrow> Kernel_Object"
  where"create_kernel_obj s pa ia ad \<equiv> 
  \<lparr> obj_attr = pa,
    info_attr = ia,
    addr = ad,
    data = None
   \<rparr>"

definition assign_hid :: "Sys_State \<Rightarrow> Pid \<Rightarrow> TEE_ObjectHandle"
  where "assign_hid s pid \<equiv>
  SOME hid . (proc_handles(the(procs s pid)) hid = None)"

definition put_kernel_obj_in_proc :: "Sys_State \<Rightarrow> Sys_Conf \<Rightarrow> Pid \<Rightarrow> Kid \<Rightarrow> Sys_State \<times>(Kernel_Object option)"
  where "put_kernel_obj_in_proc s sc pid kid \<equiv>  
  if
    is_memories_conflicted s (obj_addr_conf(the(kernel_objs_conf(sc) kid)))
  then
    (s,None)
  else
    let
       kernel_obj = get_kernel_obj_from_config sc kid;
       pa = obj_pattr_conf(kernel_obj);
       ia = obj_infoattr_conf(kernel_obj);
       ad = obj_addr_conf(kernel_obj);
       rs = obj_rights_conf(kernel_obj);
       new_obj = create_kernel_obj s pa ia ad;
       processes = procs s;
       p = the(processes pid);
       hid = assign_hid s pid;
       hds = proc_handles(p);
       cap = the(hds hid);
       objects = kernel_objs(s);
       mems = memories(s)
    in
       (s\<lparr> procs := 
            processes(pid := 
                    Some(p\<lparr> proc_handles := 
                              hds(hid := Some(cap\<lparr> kernel_obj_id := kid, rights :=rs\<rparr>)) 
                          \<rparr>)
                    ),
          kernel_objs := 
            objects(kid := Some(new_obj)), 
           memories :=  insert ad mems
          \<rparr>,
        Some(new_obj))"

definition get_object_handle:: "Sys_State \<Rightarrow> Pid \<Rightarrow> Kid \<Rightarrow> TEE_ObjectHandle option"
  where "get_object_handle s pid kid \<equiv>
  if
    \<exists> hid . procs s pid \<noteq> None \<and>
    kernel_obj_id(the(proc_handles(the(procs s pid)) hid)) = kid
  then
    Some(SOME hid . procs s pid \<noteq> None \<and>
    kernel_obj_id(the(proc_handles(the(procs s pid)) hid)) = kid)
  else
    None"

definition is_right_in_object_handle :: "Right set \<Rightarrow> Right \<Rightarrow> bool"
  where"is_right_in_object_handle rs r \<equiv> r \<in> rs"

definition is_not_same_cap :: "Sys_State \<Rightarrow> Pid \<Rightarrow> cap \<Rightarrow> bool"
  where "is_not_same_cap s pid ocap \<equiv>
  \<nexists> hid . proc_handles(the(procs(s) pid)) hid = Some(ocap)"

definition copy_object_handle :: "Sys_State \<Rightarrow> Pid \<Rightarrow> cap \<Rightarrow> Right set \<Rightarrow> Sys_State \<times> (TEE_ObjectHandle option)"
  where"copy_object_handle s pid ocap rs \<equiv>
  if
    (\<not>is_right_in_object_handle rs Copy) \<or>
    (\<not>is_not_same_cap s pid ocap)
  then
    let
      new_hid = assign_hid s pid;
      processes = procs s;
      p = the(processes pid);
      hds = proc_handles p
    in
      (s\<lparr> procs := 
            processes(pid := 
                    Some(p\<lparr> proc_handles := 
                              hds(new_hid := Some(ocap)) 
                          \<rparr>)
                    )
          \<rparr>,Some(new_hid))
  else
    (s,None)"

definition use_handle_get_obj_rights :: "Sys_State \<Rightarrow> Pid \<Rightarrow> TEE_ObjectHandle \<Rightarrow> Right set"
  where"use_handle_get_obj_rights s pid hid \<equiv> 
  let
    p = the(procs s pid);
    hds = proc_handles(p);
    cap = the(hds hid);
    rs = rights(cap)
  in
    rs"

definition get_kernel_obj :: "Sys_State \<Rightarrow> Kid \<Rightarrow> Kernel_Object"
  where "get_kernel_obj s kid \<equiv>
   the(kernel_objs s kid)"

definition is_target_kernel_obj_type ::"PobjAttribute  \<Rightarrow> SysResrcType \<Rightarrow> bool"
  where "is_target_kernel_obj_type poa t \<equiv>
    resrcid_type(pobjattr_objid(poa)) = t"

definition use_object_handle_get_cap :: "Sys_State \<Rightarrow> Pid \<Rightarrow> TEE_ObjectHandle \<Rightarrow> cap"
  where "use_object_handle_get_cap s pid hid \<equiv>
  let
    processes = procs s;
    p = the(processes pid);
    hds = proc_handles(p);
    ocap = the(hds hid)
  in
    ocap"

definition trans_object_handle :: "Sys_State \<Rightarrow> cap \<Rightarrow> Pid \<Rightarrow> Right set \<Rightarrow> Sys_State \<times> (TEE_ObjectHandle option)"
  where "trans_object_handle s ocap dst_pid rs \<equiv>
  if
     (\<not>is_right_in_object_handle rs Grant)
  then
    (s,None)
  else
    let
      new_hid = assign_hid s dst_pid;
      processes = procs s;
      p = the(processes dst_pid);
      hds = proc_handles(p)
    in
      (s\<lparr> procs := 
            processes(dst_pid := 
                    Some(p\<lparr> proc_handles := 
                              hds(new_hid := Some(ocap)) 
                          \<rparr>)
                    )
          \<rparr>,None)"

definition is_other_in_proc :: "Sys_State \<Rightarrow> Pid \<Rightarrow> TEE_ObjectHandle \<Rightarrow> Kid \<Rightarrow> bool"
  where "is_other_in_proc s pid src_hid kid \<equiv>
  \<exists> hid . hid \<noteq> src_hid \<and> 
          procs s pid \<noteq> None \<and> 
          proc_handles(the(procs s pid)) hid \<noteq> None \<and>
          kernel_obj_id(the(proc_handles(the(procs s pid)) hid)) = kid"

definition is_in_other_proc :: "Sys_State \<Rightarrow> Pid \<Rightarrow> Kid \<Rightarrow> bool" 
  where "is_in_other_proc s pid kid \<equiv>
  \<exists> hid o_pid . o_pid \<noteq> pid \<and> 
                procs s o_pid \<noteq> None \<and> 
                proc_handles(the(procs s o_pid)) hid \<noteq> None \<and>
                kernel_obj_id(the(proc_handles(the(procs s o_pid)) hid)) = kid"

definition close_object_handle:: "Sys_State \<Rightarrow> Pid \<Rightarrow> TEE_ObjectHandle \<Rightarrow> Sys_State"
  where "close_object_handle s pid hid \<equiv>
  let
    processes = procs s;
    p = the(processes pid);
    hds = proc_handles(p)
  in
    s \<lparr> procs := processes(pid := Some(p\<lparr> proc_handles := hds(hid := None) \<rparr>)) \<rparr>"

definition close_object_handle_and_obj:: "Sys_State \<Rightarrow> Pid \<Rightarrow> TEE_ObjectHandle \<Rightarrow> Kid  \<Rightarrow> Sys_State"
  where "close_object_handle_and_obj s pid hid kid \<equiv>
  let
    processes = procs s;
    p = the(processes pid);
    hds = proc_handles(p);
    kernel_objects = kernel_objs s
  in
    s \<lparr> procs := processes(pid := Some(p\<lparr> proc_handles := hds(hid := None) \<rparr>)),
        kernel_objs := kernel_objects(kid := None) \<rparr>"


definition read_data_from_obj :: "Kernel_Object \<Rightarrow> Data option"
  where "read_data_from_obj old_obj \<equiv>
  data(old_obj)"

definition write_data_to_obj :: "Kernel_Object \<Rightarrow> Data \<Rightarrow> Kernel_Object"
  where "write_data_to_obj old_obj d \<equiv>
  old_obj\<lparr>
    data := Some(d)
  \<rparr>"

definition use_object_handle_get_kid :: "Sys_State \<Rightarrow> Pid \<Rightarrow> TEE_ObjectHandle \<Rightarrow> Kid"
  where "use_object_handle_get_kid s pid hid \<equiv>
  let
    p = the(procs s pid);
    hds = proc_handles(p);
    cap = the(hds hid);
    kid = kernel_obj_id(cap)
  in
    kid"

definition read_data :: "Sys_State \<Rightarrow> Pid \<Rightarrow> Kid \<Rightarrow> Sys_State \<times> (Data option)"
  where "read_data s pid kid \<equiv>
  if
    (get_object_handle s pid kid = None) \<or>
    (\<not>is_right_in_object_handle (use_handle_get_obj_rights s kid (the(get_object_handle s pid kid))) Read)
  then
    (s,None)
  else
    let
      pid = use_object_handle_get_kid s kid (the(get_object_handle s pid kid));
      kernel_objects = kernel_objs s;
      old_obj = get_kernel_obj s kid;
      d = read_data_from_obj old_obj
    in
      (s,d)"

definition write_data :: "Sys_State \<Rightarrow> Pid \<Rightarrow> Kid \<Rightarrow> Data \<Rightarrow> Sys_State \<times> (Data option)"
  where "write_data s pid kid d \<equiv>
  if
    (get_object_handle s pid kid = None) \<or>
    (\<not>is_right_in_object_handle (use_handle_get_obj_rights s kid (the(get_object_handle s pid kid))) Write)
  then
    (s,None)
  else
    let
      kid = use_object_handle_get_kid s kid (the(get_object_handle s pid kid));
      kernel_objects = kernel_objs s;
      old_obj = get_kernel_obj s kid;
      new_obj = write_data_to_obj old_obj d
    in
      (s\<lparr>kernel_objs :=
          kernel_objects(kid := Some(new_obj))
        \<rparr>,
       Some(d))"

section "Interface definition"

definition utee_obj_create ::"Sys_State \<Rightarrow> Sys_Conf  \<Rightarrow> SubjAttribute \<Rightarrow> PobjAttribute \<Rightarrow> Sys_State \<times> (Kernel_Object option)"
  where "utee_obj_create s sc pa poa \<equiv>
  if
    (\<not>is_proc_exist s pa) \<or>
    (\<not>is_kernel_obj_conf_exist sc (get_poa_id poa)) \<or>
    (is_kernel_obj_exist s poa) \<or>
    (\<not>proc_right_check s Create (get_pa_id pa))\<or>
    (\<not>is_uid_in_poa pa poa)
  then
    (s,None)
  else
    let
      pid = get_pa_id pa;
      kid = get_poa_id poa
    in
      put_kernel_obj_in_proc s sc pid kid"

definition utee_obj_read ::"Sys_State \<Rightarrow> SubjAttribute \<Rightarrow> PobjAttribute \<Rightarrow> Sys_State \<times> (Data option)"
  where "utee_obj_read s pa poa \<equiv>
  if
    (\<not>is_proc_exist s pa) \<or>
    (\<not>is_kernel_obj_exist s poa) \<or>
    (\<not>is_uid_in_poa pa poa)
  then
    (s,None)
  else
    let
      pid = get_pa_id pa;
      kid = get_poa_id poa
    in
      read_data s pid kid"

definition utee_obj_write ::"Sys_State \<Rightarrow> SubjAttribute \<Rightarrow> PobjAttribute \<Rightarrow> Data \<Rightarrow> Sys_State \<times> (Data option)"
  where "utee_obj_write s pa poa d \<equiv>
  if
    (\<not>is_proc_exist s pa) \<or>
    (\<not>is_kernel_obj_exist s poa) \<or>
    (\<not>is_uid_in_poa pa poa)
  then
    (s,None)
  else
    let
      pid = get_pa_id pa;
      kid = get_poa_id poa
    in
      write_data s pid kid d"

definition utee_obj_copy :: "Sys_State \<Rightarrow> SubjAttribute \<Rightarrow> PobjAttribute \<Rightarrow> Right \<Rightarrow>Sys_State \<times> (TEE_ObjectHandle option)"
  where "utee_obj_copy s pa poa r \<equiv>
  if
    (\<not>is_proc_exist s pa) \<or>
    (\<not>is_kernel_obj_exist s poa) \<or>
    (get_object_handle s (get_pa_id pa) (get_poa_id poa) = None) \<or>
    (\<not>is_uid_in_poa pa poa)\<or>
    (r = Copy)
  then
    (s,None)
  else
    let
      pid = get_pa_id pa;
      kid = get_poa_id poa;
      hid = the(get_object_handle s pid kid);
      rs = use_handle_get_obj_rights s pid hid;
      ocap = \<lparr> kernel_obj_id = kid, rights = {r} \<rparr>
    in
      copy_object_handle s pid ocap rs"



definition utee_obj_close ::"Sys_State \<Rightarrow> SubjAttribute \<Rightarrow> PobjAttribute \<Rightarrow> Sys_State \<times> (Kid option)"
  where "utee_obj_close s pa poa \<equiv>
  if
    (\<not>is_proc_exist s pa) \<or>
    (\<not>is_kernel_obj_exist s poa) \<or>
    (\<not>is_uid_in_poa pa poa) \<or>
    (\<not>proc_right_check s Delete (get_pa_id pa)) \<or>
    (get_object_handle s (get_pa_id pa) (get_poa_id poa) = None)
  then
    (s,None)
  else
    let
      pid = get_pa_id pa;
      kid = get_poa_id poa;
      hid = the(get_object_handle s pid kid)
    in
      if
        (is_in_other_proc s pid kid) \<or>
        (is_other_in_proc s pid hid kid)
      then
        (close_object_handle s pid hid,Some(kid))
      else
        (s,None)"

definition utee_obj_del ::"Sys_State \<Rightarrow> SubjAttribute \<Rightarrow> PobjAttribute \<Rightarrow> Sys_State \<times> (Kid option)"
  where "utee_obj_del s pa poa \<equiv>
  if
    (\<not>is_proc_exist s pa) \<or>
    (\<not>is_kernel_obj_exist s poa) \<or>
    (\<not>is_uid_in_poa pa poa) \<or>
    (\<not>proc_right_check s Delete (get_pa_id pa)) \<or>
    (get_object_handle s (get_pa_id pa) (get_poa_id poa) = None)
  then
    (s,None)
  else
    let
      pid = get_pa_id pa;
      kid = get_poa_id poa;
      hid = the(get_object_handle s pid kid)
    in
      if
        (is_in_other_proc s pid kid) \<or>
        (is_other_in_proc s pid hid kid)
      then
        (s,None)
      else
        (close_object_handle_and_obj s pid hid kid,None)"

definition utee_channel_transmit :: "Sys_State \<Rightarrow>SubjAttribute \<Rightarrow> SubjAttribute \<Rightarrow> PobjAttribute \<Rightarrow> PobjAttribute \<Rightarrow> Sys_State \<times> (TEE_ObjectHandle option)"
  where "utee_channel_transmit s src_pa dst_pa channel_poa trans_poa \<equiv>
  if
    (\<not>is_proc_exist s src_pa) \<or>
    (\<not>is_proc_exist s dst_pa) \<or>
    get_pa_id src_pa = get_pa_id dst_pa \<or>
    (\<not>is_kernel_obj_exist s channel_poa)\<or>
    (\<not>is_kernel_obj_exist s trans_poa) \<or>
    (\<not>is_target_kernel_obj_type channel_poa CHANNEL)\<or>
    (is_target_kernel_obj_type trans_poa CHANNEL) \<or>
    (\<not>is_uid_in_poa src_pa channel_poa) \<or>
    (\<not>is_uid_in_poa src_pa trans_poa ) \<or>
    (get_object_handle s (get_pa_id src_pa) (get_poa_id channel_poa) = None) \<or>
    (get_object_handle s (get_pa_id src_pa) (get_poa_id trans_poa) = None)
  then
    (s,None)
  else
    let 
      src_pid = get_pa_id src_pa;
      src_kid = get_poa_id trans_poa;
      dst_pid = get_pa_id dst_pa;
      t_hid = the(get_object_handle s src_pid src_kid);
      ocap = use_object_handle_get_cap s src_pid t_hid;
      rs = rights(ocap)
    in
      trans_object_handle s ocap dst_pid rs"

definition mbedtls_debug_print_buf ::"Sys_State \<Rightarrow> SubjAttribute \<Rightarrow> PobjAttribute \<Rightarrow> Sys_State \<times> (Data option)"
  where "mbedtls_debug_print_buf s pa poa \<equiv>
  if
    (\<not>is_proc_exist s pa) \<or>
    (\<not>is_kernel_obj_exist s poa) \<or>
    (get_object_handle s (get_pa_id pa) (get_poa_id poa) = None) \<or>
    (\<not>is_uid_in_poa pa poa)\<or>
    (roleid_type(subjattr_callerid(pa)) = Usr Debug)
  then
    (s,None)
  else
    let
      pid = get_pa_id pa;
      kid = get_poa_id poa;
      obj = get_kernel_obj s kid
    in
      (s,data(obj))"
end

#
