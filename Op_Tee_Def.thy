theory Op_Tee_Def
  imports Main "../attr/SubjAttribute" "../attr/ObjAttribute" "../attr/InfoAttribute" "../State_Machine"

begin
section"Define basic properties"

section "datatype"
datatype Right = Read | Write | Create | Grant | Delete | Copy

datatype Privilege_Level = User | Privilege

datatype Mode = REE | TEE Privilege_Level

type_synonym Pid = SysName
type_synonym Kid = SysName
type_synonym Cid =nat
type_synonym Address = nat
type_synonym Len = nat
type_synonym TEE_ObjectHandle = nat

typedecl Data

record Addr = 
  start::Address
  size::Len

subsection"System Config"
record Proc_Conf = 
  proc_subattr_conf:: SubjAttribute
  proc_addr_conf:: Addr
  proc_rights_conf :: "Right set"

record Kernel_Obj_Conf =
  obj_pattr_conf :: PobjAttribute
  obj_infoattr_conf::InfoAttribute
  obj_addr_conf::Addr
  obj_rights_conf :: "Right set"

type_synonym Kernel_Objs_Conf = "Kid \<rightharpoonup> Kernel_Obj_Conf"

type_synonym Procs_Conf = "Pid \<rightharpoonup> Proc_Conf"

record Sys_Conf =
  kerneler_conf :: Pid
  cpus_conf :: "Cid set"
  procs_conf :: Procs_Conf
  kernel_objs_conf :: Kernel_Objs_Conf

subsection"System State"
record Kernel_Object =
  obj_attr :: PobjAttribute
  info_attr :: InfoAttribute
  addr::Addr
  data :: "Data option"

record cap =  kernel_obj_id :: Kid
              rights :: "Right set"

type_synonym Handles = "TEE_ObjectHandle \<rightharpoonup> cap"

record Process =
  proc_handles :: Handles
  proc_attr:: SubjAttribute
  proc_addr :: Addr
  proc_rights :: "Right set"

type_synonym CPUs = "Cid \<rightharpoonup> Pid"

type_synonym Kernel_Objs = "Kid \<rightharpoonup> Kernel_Object"

type_synonym Procs = "Pid \<rightharpoonup> Process"

record Sys_State =
  currents:: CPUs
  kernel_objs :: "Kernel_Objs"
  procs :: "Procs"
  memories::"Addr set"
  mode :: Mode

subsection"System Event"
datatype Sys_Call = 
        TEE_OBJ_CREATE Sys_Conf PobjAttribute |
        (*TEE_OBJ_WRITE Cid TEE_ObjectHandle Data |
        TEE_OBJ_READ Cid TEE_ObjectHandle |*)
        TEE_OBJ_COPY PobjAttribute Right | 
        TEE_OBJ_CLOSE PobjAttribute | 
        TEE_OBJ_DEL PobjAttribute |
        TEE_OBJ_TRANS SubjAttribute PobjAttribute PobjAttribute
        

datatype Kernel_Event = 
        TEE_OBJ_DEBUG PobjAttribute

datatype Event =  
        sys_call Sys_Call SubjAttribute |
        kernel_event Kernel_Event SubjAttribute

definition get_current_sid::"Sys_State \<Rightarrow> Cid \<Rightarrow> Pid"
  where "get_current_sid s cid \<equiv> (the((currents s) cid))"

definition is_kernel :: "Sys_Conf \<Rightarrow> Pid \<Rightarrow> bool"
  where "is_kernel sc pid \<equiv> pid = kerneler_conf sc"

definition is_proc :: "Sys_Conf \<Rightarrow> Pid \<Rightarrow> bool"
  where "is_proc sc pid \<equiv>
  procs_conf sc pid \<noteq> None"
end