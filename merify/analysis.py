import logging
import math
import six
from opcodes import *
from z3 import *
from z3.z3util import *
from vargenerator import *
from utils import *
import global_params


log = logging.getLogger(__name__)
SAFE_FLAG = 0
TAINT_FLAG= 1
# THIS IS TO DEFINE A SKELETON FOR ANALYSIS
# FOR NEW TYPE OF ANALYSIS: add necessary details to the skeleton functions

def set_cur_file(c_file):
    global cur_file
    cur_file = c_file

def init_analysis():
    analysis = {
        "gas": 0,
        "gas_mem": 0,
        "reentrancy_bug":[],
        #yzq
        "prng_bug":[],
        "dos_bug":[],
    }
    return analysis
#yzq:
def check_prng_bug(opcode, taint_path_conditions, global_state,taint_stack_prng,current_block_path,current_path_model):
    for expr in taint_path_conditions:
        if expr:
            global_params.BUG_TEST_CASE["PRNG"][global_state["pc"]] = current_path_model
            global_params.BUG_PC["PRNG"][global_state["pc"]] = str(global_state["pc"]) + " : " + str(opcode)+" : pathcondition"
            global_params.BUG_BLOCK_PATH["PRNG"][global_state["pc"]] = current_block_path
            return True
    if opcode == "CALL":
        if taint_stack_prng[1]:
            global_params.BUG_TEST_CASE["PRNG"][global_state["pc"]] = current_path_model
            global_params.BUG_PC["PRNG"][global_state["pc"]] = str(global_state["pc"]) + ": " + str(opcode) + " : call target"
            global_params.BUG_BLOCK_PATH["PRNG"][global_state["pc"]] = current_block_path
            return True

    if opcode == "SSTORE" and len(taint_stack_prng)>0:
        if taint_stack_prng[0]:
            global_params.BUG_TEST_CASE["PRNG"][global_state["pc"]] = current_path_model
            global_params.BUG_PC["PRNG"][global_state["pc"]] = str(global_state["pc"]) + ": " +str(opcode) + " : store address"
            global_params.BUG_BLOCK_PATH["PRNG"][global_state["pc"]] = current_block_path
            return True
        if taint_stack_prng[1]:
            global_params.BUG_TEST_CASE["PRNG"][global_state["pc"]] = current_path_model
            global_params.BUG_PC["PRNG"][global_state["pc"]] = str(global_state["pc"]) + ": " +str(opcode) + " : store value"
            global_params.BUG_BLOCK_PATH["PRNG"][global_state["pc"]] = current_block_path
            return True
    return False


def check_dos_bug(opcode, stack, taint_stack, global_state, current_block_path, current_path_model):
    if len(stack) >= 2:
        expr = stack[1]
        if not is_expr(expr):
            return False
        list_vars = get_vars(expr)
        for var in list_vars:
            #print(str(var))
            if "call_return_bool" in str(var) and not ("taint" in str(var)):
                global_params.BUG_TEST_CASE["DOS"][global_state["pc"]] = current_path_model
                global_params.BUG_PC["DOS"][global_state["pc"]] = str(global_state["pc"]) + ": " + str(opcode) + " : a function wait for call return bool to continue otherwise revert"
                global_params.BUG_BLOCK_PATH["DOS"][global_state["pc"]] = current_block_path
                return True
        return False
    else:
        raise ValueError('STACK underflow')
# Check if this call has the Reentrancy bug
# Return true if it does, false otherwise
def check_reentrancy_bug(opcode, path_conditions_and_vars, stack, global_state, taint_stack, current_block_path, current_path_model):
    path_condition = path_conditions_and_vars["path_condition"]
    new_path_condition = []
    for expr in path_condition:
        if not is_expr(expr):
            continue
        list_vars = get_vars(expr)
        for var in list_vars:
            # check if a var is global
            if is_storage_var(var):
                pos = get_storage_position(var)
                if pos in global_state['Ia']:
                    new_path_condition.append(var == global_state['Ia'][pos])
    transfer_amount = stack[2]

    taint_recipient = taint_stack[1]
    taint_transfer_amount = taint_stack[2]
    target_recipient = ""
    target_transfer_amount= ""
    if taint_recipient == 1:
        target_recipient = "taint_target"
    if taint_transfer_amount == 1:
        target_transfer_amount = "taint transfer amount"

    if isSymbolic(transfer_amount) and is_storage_var(transfer_amount):
        pos = get_storage_position(transfer_amount)
        if pos in global_state['Ia']:
            new_path_condition.append(global_state['Ia'][pos] != 0)
    if global_params.DEBUG_MODE:
        log.info("=>>>>>> New PC: " + str(new_path_condition))

    solver = Solver()
    solver_owner = Solver()
    solver_amount = Solver()
    solver.set("timeout", global_params.TIMEOUT)
    solver.add(path_condition)
    solver.add(new_path_condition)
    solver_owner.set("timeout", global_params.TIMEOUT)
    solver_owner.add(path_condition)
    solver_owner.add(new_path_condition)
    solver_amount.set("timeout", global_params.TIMEOUT)
    solver_amount.add(path_condition)
    solver_amount.add(new_path_condition)
    # 2300 is the outgas used by transfer and send.
    # If outgas > 2300 when using call.gas.value then the contract will be considered to contain reentrancy bug
    solver.add(stack[0] > 2300)
    solver_amount.add(stack[0]>2300)
    solver_owner.add(stack[0]>2300)
    ret_val = not (solver.check() == unsat)
    if ret_val:
        ms_condition = ""
        for condition in path_condition:
            if (str(condition).find('Is) ==') >= 0) or (str(condition).find("== Extract(159, 0, Is)") >= 0):
                ms_condition = str(condition)
                break
        if ms_condition != "":
            ms_owner = ms_condition.find("Ia_store")
            if ms_owner >= 0:
                ms_owner_key = ms_condition.split('-')
                try:
                    ms_owner_num = int(ms_owner_key[1])
                except:
                    ms_owner_num = str(ms_owner_key[1])
                if not (ms_owner_num in global_params.TREE):
                    global_params.TREE[ms_owner_num] = []

        if taint_recipient:
            target = str(stack[1])
            if not(target in global_params.TREE):
                global_params.TREE[target] = []
            if not(target in global_params.TARGET):
                global_params.TARGET.append(target)
                global_params.TARGET_PC[target] = []

            if not(global_state["pc"] in global_params.TARGET_PC[target]):
                global_params.TARGET_PC[target].append(global_state["pc"])
                global_params.BUG_TEST_CASE["REENTRANCY"][global_state["pc"]] = current_path_model
                global_params.BUG_PC["REENTRANCY"][global_state["pc"]] = str(global_state["pc"]) + ": " + str(opcode)
                global_params.BUG_BLOCK_PATH["REENTRANCY"][global_state["pc"]] = current_block_path
            if ms_condition!= "":
                global_params.TREE[target].append(ms_owner_num)
                if not (target in global_params.MODIFIER):
                    global_params.MODIFIER[target] = []
                    global_params.D_MODIFIER[target] = []
                    global_params.MODIFIER[target].append(ms_owner_num)
                    global_params.D_MODIFIER[target].append(ms_owner_num)
                else:
                    global_params.MODIFIER[target].append(ms_owner_num)
                    global_params.D_MODIFIER[target].append(ms_owner_num)
            elif ms_condition == "" :
                global_params.D_TAINT.append(target)

        else:
            for single in stack:
                res = str(single).find("Ia_store")
                if res >= 0:
                    result = str(single).split('-')
                    try:
                        res1 = int(result[1])
                    except:
                        res1 = str(result[1])
                        # result.append(res1[1])
                    if not (res1 in global_params.TREE):
                        global_params.TREE[res1] = []

                    if not (res1 in global_params.TARGET):
                        global_params.TARGET.append(res1)
                        global_params.TARGET_PC[res1] = []
                        global_params.TARGET_PC[res1].append(global_state["pc"])
                    elif not(global_state["pc"] in global_params.TARGET_PC[res1]):
                        global_params.TARGET_PC[res1].append(global_state["pc"])
                    if ms_condition != "":
                        if not (res1 in global_params.MODIFIER):
                            global_params.MODIFIER[res1] = []
                            global_params.MODIFIER[res1].append(ms_owner_num)
                        else:
                            global_params.MODIFIER[res1].append(ms_owner_num)
        global_params.globals_state = global_state

    return ret_val

def calculate_gas(opcode, stack, mem, global_state, analysis, solver):
    gas_increment = get_ins_cost(opcode) # base cost
    gas_memory = analysis["gas_mem"]
    # In some opcodes, gas cost is not only depend on opcode itself but also current state of evm
    # For symbolic variables, we only add base cost part for simplicity
    if opcode in ("LOG0", "LOG1", "LOG2", "LOG3", "LOG4") and len(stack) > 1:
        if isReal(stack[1]):
            gas_increment += GCOST["Glogdata"] * stack[1]
    elif opcode == "EXP" and len(stack) > 1:
        if isReal(stack[1]) and stack[1] > 0:
            gas_increment += GCOST["Gexpbyte"] * (1 + math.floor(math.log(stack[1], 256)))
    elif opcode == "EXTCODECOPY" and len(stack) > 2:
        if isReal(stack[2]):
            gas_increment += GCOST["Gcopy"] * math.ceil(stack[2] / 32)
    elif opcode in ("CALLDATACOPY", "CODECOPY") and len(stack) > 3:
        if isReal(stack[3]):
            gas_increment += GCOST["Gcopy"] * math.ceil(stack[3] / 32)
    elif opcode == "SSTORE" and len(stack) > 1:
        if isReal(stack[1]):
            try:
                try:
                    storage_value = global_state["Ia"][int(stack[0])]
                except:
                    storage_value = global_state["Ia"][str(stack[0])]
                # when we change storage value from zero to non-zero
                if storage_value == 0 and stack[1] != 0:
                    gas_increment += GCOST["Gsset"]
                else:
                    gas_increment += GCOST["Gsreset"]
            except: # when storage address at considered key is empty
                if stack[1] != 0:
                    gas_increment += GCOST["Gsset"]
                elif stack[1] == 0:
                    gas_increment += GCOST["Gsreset"]
        else:
            try:
                try:
                    storage_value = global_state["Ia"][int(stack[0])]
                except:
                    storage_value = global_state["Ia"][str(stack[0])]
                solver.push()
                solver.add(Not( And(storage_value == 0, stack[1] != 0) ))
                if solver.check() == unsat:
                    gas_increment += GCOST["Gsset"]
                else:
                    gas_increment += GCOST["Gsreset"]
                solver.pop()
            except Exception as e:
                if str(e) == "canceled":
                    solver.pop()
                solver.push()
                solver.add(Not( stack[1] != 0 ))
                if solver.check() == unsat:
                    gas_increment += GCOST["Gsset"]
                else:
                    gas_increment += GCOST["Gsreset"]
                solver.pop()
    elif opcode == "SUICIDE" and len(stack) > 1:
        if isReal(stack[1]):
            address = stack[1] % 2**160
            if address not in global_state:
                gas_increment += GCOST["Gnewaccount"]
        else:
            address = str(stack[1])
            if address not in global_state:
                gas_increment += GCOST["Gnewaccount"]
    elif opcode in ("CALL", "CALLCODE", "DELEGATECALL") and len(stack) > 2:
        # Not fully correct yet
        gas_increment += GCOST["Gcall"]
        if isReal(stack[2]):
            if stack[2] != 0:
                gas_increment += GCOST["Gcallvalue"]
        else:
            solver.push()
            solver.add(Not (stack[2] != 0))
            #if check_sat(solver) == unsat:
                #gas_increment += GCOST["Gcallvalue"]
            solver.pop()
    elif opcode == "SHA3" and isReal(stack[1]):
        pass # Not handle


    #Calculate gas memory, add it to total gas used
    length = len(mem.keys()) # number of memory words
    new_gas_memory = GCOST["Gmemory"] * length + (length ** 2) // 512
    gas_increment += new_gas_memory - gas_memory

    return (gas_increment, new_gas_memory)

def update_analysis(analysis, opcode, stack, mem, global_state, path_conditions_and_vars, taint_path_conditions, solver,taint_stack,taint_stack_prng, current_block_path, current_path_model):
    gas_increment, gas_memory = calculate_gas(opcode, stack, mem, global_state, analysis, solver)
    analysis["gas"] += gas_increment
    analysis["gas_mem"] = gas_memory
    if opcode == "JUMPI":
        dos_result = check_dos_bug(opcode, stack, taint_stack, global_state, current_block_path, current_path_model)
        analysis["dos_bug"].append(dos_result)

    if opcode == "CALL":
        recipient = stack[1]
        transfer_amount = stack[2]
        if isSymbolic(recipient):
            recipient = simplify(recipient)
        reentrancy_result = check_reentrancy_bug(opcode,path_conditions_and_vars, stack, global_state, taint_stack, current_block_path, current_path_model)
        analysis["reentrancy_bug"].append(reentrancy_result)



        #yzq
        prng_result = check_prng_bug(opcode, taint_path_conditions, global_state, taint_stack_prng, current_block_path,current_path_model)
        analysis["prng_bug"].append(prng_result)

    elif opcode == "SSTORE":
        # yzq
        prng_result = check_prng_bug(opcode, taint_path_conditions, global_state, taint_stack_prng, current_block_path, current_path_model)
        analysis["prng_bug"].append(prng_result)




