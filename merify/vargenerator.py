class Generator:
    def __init__(self):
        self.countstack = 0
        self.countdata = 0
        self.count = 0

    # def gen_stack_var(self):
    #     self.countstack += 1
    #     return "s" + str(self.countstack)

    # def gen_data_var(self):
    #     self.countdata += 1
    #     return "Id_" +

    def gen_data_var(self, position,pc):
        self.countdata += 1
        return "Id_" + str(position)+"_"+str(pc)

    def gen_data_size(self,pc):
        return "Id_size_"+str(pc)

    def gen_mem_var(self, address,pc):
        return "mem_" + str(address)+"_"+str(pc)

    def gen_arbitrary_var(self,pc):
        self.count += 1
        return "some_var_" + str(self.count)+"_"+str(pc)

    def gen_arbitrary_address_var(self,pc):
        self.count += 1
        return "some_address_" + str(self.count)+"_"+str(pc)

    def gen_owner_store_var(self, position, var_name="", pc=0):
        return "Ia_store-%s-%s_%s" % (str(position), var_name, str(pc))

    def gen_gas_var(self,pc):
        self.count += 1
        return "gas_" +str(self.count)+"_" +str(pc)

    def gen_gas_price_var(self):
        return "Ip"

    def gen_address_var(self):
        return "Ia"

    def gen_caller_var(self):
        return "Is"

    def gen_origin_var(self):
        return "Io"

    def gen_balance_var(self,pc):
        self.count += 1
        return "balance_" + str(self.count)+"_"+str(pc)

    def gen_code_var(self, address, position, bytecount, pc):
        return "code_" + str(address) + "_" + str(position) + "_" + str(bytecount)+"_"+str(pc)

    def gen_code_size_var(self, address,pc):
        return "code_size_" + str(address)+"_"+str(pc)

    def gen_call_return_var(self,isTaint,pc):
        if isTaint:
            return "call_return_bool_taint"+str(pc)
        else:
            return "call_return_bool_"+str(pc)
