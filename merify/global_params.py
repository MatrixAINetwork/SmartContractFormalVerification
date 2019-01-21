
REPORT_MODE = 0

#for testing output mode
EVAL = 0
#print everything in the console
PRINT_MODE = 0

# enable log file to print all exception
DEBUG_MODE = 0

reportName = ""

# check false positive in concurrency
CHECK_CONCURRENCY_FP = 0

# Timeout for z3 in ms
TIMEOUT = 1000

# Set this flag to 2 if we want to do evm real value unit test
# Set this flag to 3 if we want to do evm symbolic unit test
UNIT_TEST = 0

# timeout to run symbolic execution (in secs)
GLOBAL_TIMEOUT = 10000

# timeout to run symbolic execution (in secs) for testing
GLOBAL_TIMEOUT_TEST = 2

# print path conditions
PRINT_PATHS = 0

# WEB = 1 means that we are using merify for web service
WEB = 0

# Redirect results to a json file.
STORE_RESULT = 0

# depth limit for DFS
DEPTH_LIMIT = 50

GAS_LIMIT = 4000000

LOOP_LIMIT = 3

# Use a public blockchain to speed up the symbolic execution
USE_GLOBAL_BLOCKCHAIN = 0

USE_GLOBAL_STORAGE = 0

# Take state data from state.json to speed up the symbolic execution
INPUT_STATE = 0

# Check assertions
CHECK_ASSERTIONS = 0

GENERATE_TEST_CASES = 0

# Run merify in parallel
PARALLEL = 0

VAR_STATE_GLOBAL = {}

SSTORE_STACK = {}

PATH_CONDITION = {}

TARGET_DEPTH = 2

MODIFIER_DEPTH = 2

TARGET = []

MODIFIER = {}

D_MODIFIER = {}

D_TAINT =[]

TAINT = []

GLOBAL_PC_SSTORE = {}

GLOBAL_PC_SSLOAD = {}

LAST_SSTORE = {}

PRE_OPCODE_COUNT = 0
# The relation of Global params
TREE = {}

globals_state = {}

TARGET_PC = {}

EVM_VERSION=""

TESTED_EVM_VERSION="1.8.16"

STORAGE_VALUES = {}

BUG_PC ={"PRNG":{}, "DOS":{}, "OVERFLOW":{}, "REENTRANCY":{}, "UNDERFLOW":{}, "TOD":{}, "ASSERTFAIL":{}}

BUG_BLOCK_PATH = {"PRNG":{}, "DOS":{}, "OVERFLOW":{}, "REENTRANCY":{},"UNDERFLOW":{}, "TOD":{}, "ASSERTFAIL":{}}

BUG_TEST_CASE = {"PRNG":{}, "DOS":{}, "OVERFLOW":{},"REENTRANCY":{},"UNDERFLOW":{}, "TOD":{},"ASSERTFAIL":{}}

REP_BUG_NUM = {"Reentrancy": 0, "Pseudorandom Generator": 0, "Integer Overflow": 0, "Integer Underflow": 0, "Transaction-Order Dependency": 0, "Denial-of-Service": 0, "Account Integrity Violation": 0}

DOC_PATH = "."

PRIVATE_KEY = "-----BEGIN RSA PRIVATE KEY-----\n\
MIIEowIBAAKCAQEAwpwtyOyd8vy5wPtwJm2//iaKSOE7QTpSdisJI7grViUqSNUu\n\
4JXskpUI66VaX69SpSWHnHMCYyerokAv1PdD7ZJ6qTjtldxG2MQ7jr1Lvv/dYgZl\n\
I4q1D5/Kh1uvcziOpOcbFMhuZrxjZ+I6ApRoJto/QdXqZE9HCK9782ejvsjx9MsJ\n\
BxOhL28Bm/Exu3bmdahihl2qSvr/ZFV7mDf9h2Ou0IMDRK4vfKarZcpKfoSIWLtS\n\
PG6LeK6bNEYp2saOvCa5ZYx/FwAYmjcHj4A895I8UEZMN0ef+jNd7DWEyys2rvcH\n\
Gr91tVRDNBi0yZ+K/MF7Eih0/XGitWNuNn9I4QIDAQABAoIBAA8LF5byg3snAgzi\n\
4tZ1oWO6AvKDRptSMNGlnf0+3Uq5cL1UjV0a+cCS+K+Ohp/i45aUghkb4tFbXa8b\n\
GxdxTbTtn8G4/tSYxHk5Igl0pIhNKwXKzMKklD5y8aro8XUMqCojGzrOC4qxgVWk\n\
bSuJ4Usvj7g9GvNKFYmcVw6Hsmaq6z2ct6i8nzVmdvIMnC/nIWOfkXur6+Ci/KVo\n\
SnLLRLK0oAO6k+sFh4TYw3C+RJ6OGQQ9jFArrIcF+L38gqj6golc/7HN+PwGf9mJ\n\
vArbiiDlpAD3ExaRXARG+pmKLSr5810+TPImP7YCuYotfgFdBjMA6FUFCi1GDZ4g\n\
teBiIAECgYEAztzg2Y11qP4KzTyPYErZsuNKndHwCyIKTot8stVfwdQhOb6krYpe\n\
p0m6rVH1YuC0LHo9hde+909t9IwhKXTOdewG/GI52CN5+k88LuUpKgJm9bKQTk/J\n\
Kld81r744OSiKkEz5ZxGtS6DpcY2JcxmF4oerbWHAdDg/kv6/tBc8WECgYEA8NY5\n\
W12BrH5RsSm9EZdBeChMu7+TV5O5JArTvPuOlPFZKSbCW4I/O6xJqoVX6xy3as9N\n\
j954kEkQJrWfw5UbmHc1nb416NiqnARbFRKpSrlZhL2xvo3TbSoXTgxZ6eGGztG7\n\
vlNbczK0vlTEvB9VKkZQKfEg1WTyu3IVQfcQB4ECgYEAu0VXAVyBAiZKHRcQLXpV\n\
rw75g/qEt29vqT+5+iQU9mJWWfJvHvQ/UG784t9pqMQIGKPpgnuYVEfCITui4ebu\n\
6e5tPJqoBzXGvYZx03p+U5utHg0zetHcKcreJ4LnyKDy9hHlK57YnDmp0K+qYXmz\n\
iuftchD+UfSJW23pojl7isECgYBwwhwApvr7o/jjlcMr5UGF3HhwvvVhX4yjT15r\n\
cOwE2CsClV8SMR0h9zxWVjAfqEZH/980qNiR1WN2fDrc+4b8D3RO8quS5T6b5X4v\n\
k5knnzhGafo6WXTP+5EFvcqrMihH1PKt3aFHgkoVguLJoXHiZSFLQdY5kxYCpRtG\n\
00HyAQKBgGbGLJQr+4L9+oc1ALP68ChzAt4dp2KJDshhe8LxMiZeWOvImzDNwf0Z\n\
SHGTbhpSpjvWCov54UMK8i31/fpxwHxFkm0H+bOKGJg7jvZnV57pJE749GMdA1Zt\n\
F1qJ24JJczJVcbxN43hyFJ1wIRNQbC0c5Wxd5w8O2Z4fI1YnkT50\n\
-----END RSA PRIVATE KEY-----\n"
