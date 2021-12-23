from elftools.elf.elffile import ELFFile

from elftools.common.py3compat import maxint, bytes2str
from elftools.dwarf.descriptions import describe_form_class

import xml.etree.ElementTree as ET
import os.path

from ptrace.utils.utils import save_file_text, read_xml, confirm

class CFBlock:
    block_start = -1
    block_end = -1
    file_name = ""
    line_start = -1
    line_end = -1
    function_name = ""
    code = ""

    def __init__(self, block_start, block_end, file_name, line_start, line_end, function_name, code_raw):
        self.block_start = block_start
        self.block_end = block_end
        self.file_name = file_name
        self.line_start = line_start
        self.line_end = line_end
        self.function_name = function_name

        code_escaped = code_raw.translate(str.maketrans({"<":  r"\<",
                                          ">":  r">]",
                                          "\\": r"\\",
                                          "^":  r"\^",
                                          '"':  r'\"',
                                          "&":  r"\&",
                                          "'":  r'\"'}))#TODO might have to fix this
        self.code = code_escaped

    def show(self):
        print(f"[BLOCK] ({hex(self.block_start)} -> {hex(self.block_end)})\n  {self.file_name}::{self.line_start} -> {self.line_end} ({self.function_name})\n--------\n{self.code}\n--------")

    def print_range(self):
        print(f"[BLOCK] ({hex(self.block_start)} -> {hex(self.block_end)})\n")

def convert_blocks_to_xml(cfgblocks):
    xml = "<cfgblocks>\n"

    run_id = 0
    for run in cfgblocks:
        xml += f'<run id="{run_id}">\n'
        for block in run:
            xml += "<block "

            xml += f'block_start="{block.block_start}" '
            xml += f'block_end="{block.block_end}" '
            xml += f'file_name="{block.file_name}" '
            xml += f'line_start="{block.line_start}" '
            xml += f'line_end="{block.line_end}" '
            xml += f'function_name="{block.function_name}" '

            #xml += f"code='{block.code}'"
            xml += ">\n"

            #xml += block.code

            xml += "</block>\n"
        xml += "</run>\n"
        run_id += 1
    xml += "</cfgblocks>\n"
    return xml

def convert_functions_to_xml(functions):
    xml = "<functions>\n"
    for function in functions:
        xml += f"<function name=\"{function[0]}\" start=\"{function[1]}\" end=\"{function[2]}\" >"
        xml += "</function>\n"

    xml += "</functions>\n"
    return xml

def read_source(path_c):
    code_lines = [] #either open all files and search corresponding source file or justcconcat and use offset
    with open(path_c) as c_file:
        code_lines = c_file.readlines()
    #for line in code_lines:
        #print(line, end='')
    return code_lines

def read_labels(path_elf, path_c, path_trace):
    code_lines = read_source(path_c)

    tree,root = read_xml(path_trace)
    run = 0
    elf_addresses = set()
    for entry in root:
        if(entry.tag=="symex"):
            run += 1
            # index 0 = execution trace
            for child in entry[0]:
                step_attr = child.attrib
                pc_hex = step_attr.get('pc')
                pc = int(pc_hex,16)
                elf_addresses.add(pc)

                #if(child[0].tag == "load" or child[0].tag == "store"):
                #    memory_target = int(child[0].attrib.get('target'),16)
    elf_addresses = sorted(elf_addresses)
    print(f"addresses: {elf_addresses}")

    with open(path_elf, 'rb') as input_file:
        print(input_file.read(10)[0:10])
        elf_file = ELFFile(input_file)
        elf_arch = elf_file.get_machine_arch()
        print(f"Loaded a {elf_arch} binary")
        print(f"Found {elf_file.num_sections()} sections")
        #sections = None
        for i in range(elf_file.num_sections()):
            section = elf_file.get_section(i)
            print(f"{section.name: <20}START:{hex(section['sh_offset'])}")
        print()

        if not elf_file.has_dwarf_info():
            print('file has no DWARF info')
            return

        dwarfinfo = elf_file.get_dwarf_info()
        last_file = ""
        for address in elf_addresses:
            funcname = decode_funcname(dwarfinfo, address)
            file, line = decode_file_line(dwarfinfo, address)
            #print('Function:', bytes2str(funcname))
            if(file != None):
                if(last_file!=file):
                    print('\n[File]:', bytes2str(file))
                    last_file = file
                print(f'Line{line}: {code_lines[line][0:-1]}')
            else:
                print(f"address {hex(address)} out of range")


        #instructions = read_elf_instructions(elf_file,input_file,".text")
        #print(f"Total num instructions: {len(instructions)}")

def is_block_already_contained(block, block_list):
    """
    Return tuple (index of containing block, containment type) or (-1, -1) if not contained
    type: 
    0 - fully enclosed
    1 - start before start (block contains c_block)
    2 - end after ending ERROR
    -1 - None

    """
    index = -1
    counter = 0
    occurences = 0
    for c_block in block_list:
        a_start = block.block_start
        a_end = block.block_end
        b_start = c_block.block_start
        b_end = c_block.block_end
        if(a_start==b_start and a_end == b_end):
            occurences+=1 #identical or duplicate
            if(occurences>1):
                print("duplicate")
        else:
            if(a_start >= b_start and a_start <= b_end): #block is inside current block
                #print(hex(a_start),hex(a_end),hex(b_start),hex(b_end))
                return (block_list.index(c_block), 0) #end should always be identical
            else:
                if(a_start < b_start and a_end >= b_start): #or block_end == cblock_end
                    #print(a_start,a_end,b_start,b_end)
                    return (block_list.index(c_block), 1) #end should always be identical
        counter += 1
    if(occurences<1):
        print("Warning block not found")
    return (-1, -1)

def split_into_blocks(path_elf, path_c, path_trace, runs):
    cfblocks = [] # [run] [block]
    code_lines = read_source(path_c)

    tree,root = read_xml(path_trace)
    run = -1
    elf_addresses = set()
    blocks = [set() for _ in range(runs)]
    for entry in root: #either parse trace or parse binary and follow binary execution through blocks
        if(entry.tag=="symex"):
            run += 1
            print(f"run {run}")
            # index 0 = execution trace
            block_start = -1 #int(entry[0][0].attrib.get('pc'))
            block_end = block_start
            for child in entry[0]:
                step_attr = child.attrib
                pc_hex = step_attr.get('pc')
                pc = int(pc_hex,16)
                if(block_start == -1):
                    block_start = pc
                if(child[0].tag == "jump" or child[0].tag == "branch"):
                    block_end = pc
                    blocks[run].add((block_start,block_end))
                    block_start = -1
    #print(blocks)

    with open(path_elf, 'rb') as input_file:
        elf_file = ELFFile(input_file)

        if not elf_file.has_dwarf_info():
            print('file has no DWARF info')
            return

        dwarfinfo = elf_file.get_dwarf_info()
        last_file = ""
        for run in range(runs): #this can create different blocks depending on run index, but this might be actually better
            #print(f"---- [RUN {run}] ----")
            current_block_list = []
            for block in blocks[run]:
                #print(f"block {block}")
                line_start = -1
                line_end = -1
                funcname = decode_funcname(dwarfinfo, block[0])
                file_1, line_start = decode_file_line(dwarfinfo, block[0])
                file_2, line_end = decode_file_line(dwarfinfo, block[1])
                #print('Function:', bytes2str(funcname))
                if(file_1 != None and file_2 != None):
                    if(last_file!=file_1):
                        #print('\n[File]:', bytes2str(file_1))
                        last_file = file_1
                    current_lines = ""
                    for line in range(line_start, line_end):
                        #print(f'Line{line+1}: {code_lines[line][0:-1]}')#TODO is the line correct
                        current_lines += code_lines[line]
                    current_block = CFBlock(block[0], block[1], file_1, line_start, line_end, funcname, current_lines[0:-1])
                    current_block_list.append(current_block)
                else:
                    print(f"address {hex(line_end)} out of range")
                #print()
            #print()

            #cleanup blocklist
            future_blocks_to_keep = [] #blocks not yet iterated over that contain a block to delete
            blocks_to_delete = []
            for block in current_block_list:
                if(block in future_blocks_to_keep or block in blocks_to_delete):
                    #print("block not processed")
                    continue
                else:
                    contained_index, contain_type = is_block_already_contained(block, current_block_list)
                    if(contained_index!=-1):
                        #print("Block is already contained")
                        if(contain_type==0): #this block is fully contained in another
                            #block.print_range()
                            #print("is contained in")
                            #current_block_list[contained_index].print_range()
                            blocks_to_delete.append(block)
                            future_blocks_to_keep.append(current_block_list[contained_index])
                        if(contain_type==1): #this block contains a later one
                            #block.print_range()
                            #print("contains")
                            #current_block_list[contained_index].print_range()
                            blocks_to_delete.append(current_block_list[contained_index])
                    else:
                        pass
            merged_block_list = []
            for block in current_block_list:
                if(block not in blocks_to_delete):
                    merged_block_list.append(block)
                else:
                    #print("removed block")
                    #block.print_range()
                    pass

            cfblocks.append(merged_block_list)
    return cfblocks



def decode_funcname(dwarfinfo, address):
    # Go over all DIEs in the DWARF information, looking for a subprogram
    # entry with an address range that includes the given address. Note that
    # this simplifies things by disregarding subprograms that may have
    # split address ranges.
    for CU in dwarfinfo.iter_CUs():
        for DIE in CU.iter_DIEs():
            try:
                if DIE.tag == 'DW_TAG_subprogram':
                    lowpc = DIE.attributes['DW_AT_low_pc'].value

                    # DWARF v4 in section 2.17 describes how to interpret the
                    # DW_AT_high_pc attribute based on the class of its form.
                    # For class 'address' it's taken as an absolute address
                    # (similarly to DW_AT_low_pc); for class 'constant', it's
                    # an offset from DW_AT_low_pc.
                    highpc_attr = DIE.attributes['DW_AT_high_pc']
                    highpc_attr_class = describe_form_class(highpc_attr.form)
                    if highpc_attr_class == 'address':
                        highpc = highpc_attr.value
                    elif highpc_attr_class == 'constant':
                        highpc = lowpc + highpc_attr.value
                    else:
                        print('Error: invalid DW_AT_high_pc class:',
                              highpc_attr_class)
                        continue

                    if lowpc <= address <= highpc:
                        return DIE.attributes['DW_AT_name'].value
            except KeyError:
                continue
    return None


def decode_file_line(dwarfinfo, address):
    # Go over all the line programs in the DWARF information, looking for
    # one that describes the given address.
    for CU in dwarfinfo.iter_CUs():
        # First, look at line programs to find the file/line for the address
        lineprog = dwarfinfo.line_program_for_CU(CU)
        prevstate = None
        for entry in lineprog.get_entries():
            # We're interested in those entries where a new state is assigned
            if entry.state is None:
                continue
            if entry.state.end_sequence:
                # if the line number sequence ends, clear prevstate.
                prevstate = None
                continue
            # Looking for a range of addresses in two consecutive states that
            # contain the required address.
            if prevstate and prevstate.address <= address < entry.state.address:
                filename = lineprog['file_entry'][prevstate.file - 1].name
                line = prevstate.line
                return filename, line
            prevstate = entry.state
    return None, None

def decode_function_ranges(path_elf):
    functions = []#(name,start,end)
    with open(path_elf, 'rb') as input_file:
        elf_file = ELFFile(input_file)

        if not elf_file.has_dwarf_info():
            print('file has no DWARF info')
            return

        dwarfinfo = elf_file.get_dwarf_info()
        for CU in dwarfinfo.iter_CUs():
            for DIE in CU.iter_DIEs():
                try:
                    #print(DIE.tag)
                    #print(DIE.attributes['DW_AT_name'].value)
                    if DIE.tag == 'DW_TAG_subprogram':
                        lowpc = DIE.attributes['DW_AT_low_pc'].value

                        # DWARF v4 in section 2.17 describes how to interpret the
                        # DW_AT_high_pc attribute based on the class of its form.
                        # For class 'address' it's taken as an absolute address
                        # (similarly to DW_AT_low_pc); for class 'constant', it's
                        # an offset from DW_AT_low_pc.
                        highpc_attr = DIE.attributes['DW_AT_high_pc']
                        highpc_attr_class = describe_form_class(highpc_attr.form)
                        if highpc_attr_class == 'address':
                            highpc = highpc_attr.value
                        elif highpc_attr_class == 'constant':
                            highpc = lowpc + highpc_attr.value
                        else:
                            print('Error: invalid DW_AT_high_pc class:',
                                highpc_attr_class)
                            continue

                        functions.append((DIE.attributes['DW_AT_name'].value, lowpc, highpc))
                except KeyError:
                    continue
    #print(functions)
    return functions


def process_DWARF(path_dir_elf, path_dir_c, path_trace, output_path):
    #read_labels(path_dir_elf, path_dir_c, path_trace)
    path, file = os.path.split(path_trace) #path_trace.split("/")[-1].split(".")[0]
    executable_name = file.split(".")[0]

    cfg_blocks = split_into_blocks(path_dir_elf, path_dir_c, path_trace, 10)

    cfg_blocks_sorted = []
    for run in cfg_blocks:
        cfg_blocks_sorted.append(sorted(run, key=lambda b: b.block_start))

    """for run in cfg_blocks_sorted:
        print("RUN ", cfg_blocks_sorted.index(run))
        for block in run:
            block.print_range()

    print("\n")"""

    xml = '<?xml version="1.0" encoding="UTF-8"?>\n'
    xml += "<cfdata>\n"

    xml += convert_blocks_to_xml(cfg_blocks_sorted)
    functions = decode_function_ranges(path_dir_elf)

    xml += convert_functions_to_xml(functions)
    
    xml += "</cfdata>\n"

    save_file_name = f"{output_path}/{executable_name}.blk"
    if(os.path.isfile(save_file_name)):
        if(confirm(f"BLK file [{save_file_name}] already exists. Overwrite? [y/yes] ")):
            save_file_text(xml, save_file_name, True)
        else:
            print("BLK file was not saved")
    else:
        save_file_text(xml, save_file_name, False)
        print(f"Saved BLK file as [{save_file_name}]")
