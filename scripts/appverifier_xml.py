#!/usr/bin/env python3
#
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

# Built-in
import xml.etree.ElementTree as ElementTree
import argparse

s_AppVerifier_LogText = "{Application Verifier}logSession"
s_AppVerifier_EntryText = "{Application Verifier}logEntry"
s_AppVerifier_ErrorSeverities = ["Warning", "Error", "UNKNOWN"]

# A dictionary to take the error codes and convert them to basic information
# on what went wrong.
#
# How to adjust/learn more:
# To add/remove from this list, run "appverif" in a Windows terminal with
# administrator privileges and then press F1 to get the help page. Then search
# for the error code you got (minus the "0x" part at the beginning) and use the
# information there to add/adjust the entry in the dictionary below.
s_AppVerifier_ErrorCodeHelp = {
    "Exceptions": {
        "0x650": "The application is trying to run code from an address that is non-executable or free"
    },
    "Handles": {
        "0x300": "The function on the top of the stack passed an invalid handle to system routines",
        "0x301": "The function on the top of the stack passed an invalid TLS index to TLS system routines",
        "0x302": "The function on the top of the stack called WaitForMultipleObjects with NULL as the address "
        "of the array of handles to wait for or with zero as the number of handles",
        "0x303": "The function on the top of the stack passed a NULL handle to system routines",
        "0x304": "The  current thread is currently running code inside the DllMain function of one "
        "of the DLLs loaded in the current process and it calls WaitForSingleObject or "
        "WaitForMultipleObjects to wait on a thread handle in the same process",
        "0x305": "The current thread is calling an API with a handle to an object with an incorrect object type"
    },
    "Heaps": {
        "0x01": "Unknown error encountered that cannot be determined/classified by AppVerifier",
        "0x02": "The application touched non-accessible page. Typically is caused by a buffer overrun error",
        "0x03": "A heap created with HEAP_NO_SERIALIZE flag was accessed simultaneously from two threads",
        "0x04": "The size of the block in a 'HeapAlloc' or 'HeapReAlloc' operation was above any reasonable value",
        "0x05": "Heap structure did not include magic value from AppVerifier - meaning somehow the internal heap "
        "structure was corrupted or a bogus value was used as heap handle",
        "0x06": "Typically means block was allocated in one heap and freed in another",
        "0x07": "Block was freed twice",
        "0x08": "Generic error due to corruption in the heap block that AppVerifier cannot place more specifically",
        "0x09": "Tried to destroy the default process heap",
        "0x0A": "Access violation raised while executing heap manager code",
        "0x0B": "AppVerifier could not determine any particular type of corruption for the block. "
        "Generally means heap points to non-accessible memory area",
        "0x0C": "AppVerifier could not determine any particular type of corruption for the block. "
        "Generally happens if during heap free operation you pass an address that poins to a non-accessible memory area. "
        "Can also occur with double free situations",
        "0x0D": "Block of memory is written to after being freed",
        "0x0E": "Freed block marked as non-accessible had access attempt",
        "0x0F": "Magic pattern added by AppVerifier at end of heap block changed. "
        "Typically means buffer overrun errors",
        "0x10": "Buffer underruns",
        "0x11": "Buffer underruns",
        "0x12": "Buffer underruns",
        "0x13": "Non-accessible page at end of heap allocation was touched. Typically caused by a buffer overrun error",
        "0x14": "Page heap manager detected internal inconsistencies while calling GetProcessHeaps"
    },
    "Leak": {
        "0x900": "Owner DLL of the allocation was dynamically unloaded while owning resources",
        "0x901": "Owner DLL of the handle was dynamically unloaded while owning resources",
        "0x902": "Owner DLL of the registry key was dynamically unloaded while owning resources",
        "0x903": "Owner DLL of the virtual reservation was dynamically unloaded while owning resources",
        "0x904": "Owner DLL of the SysString was dynamically unloaded while owning resources",
        "0x905": "DLL registered for power notification was dynamically unloaded without registering",
        "0x906": "Owner DLL of the COM allocation was dynamically unloaded while owning resources"
    },
    "Locks": {
        "0x200": "A thread is terminated, suspended, or in a state in which it cannot hold a critical section",
        "0x201": "A DLL has a global variable containing a critical section and the DLL is unloaded but the "
        "critical section has not been deleted",
        "0x202": "A heap allocation contains a critical section, the allocation is freed, and the critical section "
        "has not been deleted",
        "0x203": "Typicaly means a critical section has been initialized more than once. May mean the critical section "
        "or its debug information structure has been corrupted",
        "0x204": "Memory containing a critical section was freed but the critical section has not been deleted using 'DeleteCriticalSection'",
        "0x205": "The DebugInfo field of the critical section is pointing to freed memory",
        "0x206": "The owner thread ID is invalid in the current context",
        "0x207": "The recursion count field of the critical section structure is invalid in the current context",
        "0x208": "A critical section is owned by a thread if it is deleted or if the critical section is uninitialized",
        "0x209": "A critical section is released more times than the current thread acquired it",
        "0x210": "A critical section is used without being initialized or after it has been deleted",
        "0x211": "A critical section is reinitialized by the current thread",
        "0x212": "The current thread is calling VirtualFree on a memory block that contains an active critical section",
        "0x213": "The current thread is calling UnmapViewOfFile on a memory block that contains an active critical section",
        "0x214": "The current thread calling LeaveCriticalSection but does not own any critical section",
        "0x215": "The current thread tries to use a private lock that lives inside another DLL"
    },
    "Memory": {
        "0x600": "AppVerifier detects a VirtualFree or a DLL unload with an invalid start adress or size of the memory allocation",
        "0x601": "AppVerifier detects a VirtualAlloc call with an invalid start adress or size of the memory allocation",
        "0x602": "AppVerifier detects a MapViewOfFile call with an invalid base address or size of the mapping",
        "0x603": "AppVerifier detects an IsBadXXXPtr call with an invalid address for the memory buffer to be probed",
        "0x604": "AppVerifier detects an IsBadXXXPtr call for a memory allocation that is free",
        "0x605": "AppVerifier detects an IsBadXXXPtr call for a memory allocation that contains at least one GUARD_PAGE",
        "0x606": "AppVerifier detects an IsBadXXXPtr call with a NULL address",
        "0x607": "AppVerifier detects an IsBadXXXPtr call with an invalid start address or invalid size for the memory buffer to be probed",
        "0x608": "AppVerifier detects a DLL unload with an invalid start address for the size of the DLL memory range",
        "0x609": "AppVerifier detects a VirtualFree for a block of memory that is actually part of the current thread's stack",
        "0x60A": "AppVerifier detects a VirtualFree with an incorrect value for the FreeType parameter",
        "0x60B": "AppVerifier detects a VirtualFree for an address that is already free",
        "0x60C": "AppVerifier detects a VirtualFree with a non-zero value for the dwSize parameter",
        "0x60D": "A DLL's entry point function is raising an exception",
        "0x60E": "A thread function is raising an exception",
        "0x60F": "An exception occured during an IsBadXXXPtr call",
        "0x610": "AppVerifier detects a VirtualFree call with a NULL first parameter",
        "0x612": "AppVerifier detects a HeapFree for a block of memory that is actually part of the current thread's stack",
        "0x613": "AppVerifier detects an UnmapViewOfFile for a block of memory that is actually part of the current thread's stack",
        "0x614": "The application is trying to use NULL or some other incorrect address as the address of a valid object",
        "0x615": "The application is trying to use NULL or some other incorrect address as the address of a valid object",
        "0x616": "The application is trying to run code from an address that is non-executable or free",
        "0x617": "An exception occurred while initializing a buffer specified as output parameter for a Win32 or (non-AWS) CRT API",
        "0x618": "An exception occurred while calling HeapSize for a heap block that is being freed",
        "0x619": "The program is calling VirtualFree with an IpAddress parameter that is not the base address returned by "
        "the VirtualAlloc or VirtualAllocEx function when the region of pages was reserved",
        "0x61A": "The program is calling UnmapViewOfFile with an IpBaseAddress parameter that is not identical to the value returned"
        "by a previous call to the MapViewOfFile or MapViewOfFileEx function",
        "0x61B": "A callback function in the threadpool thread is rasing an exception",
        "0x61C": "The application is trying to run code from an address that is non-executable or free",
        "0x61D": "The application is created an executable heap",
        "0x61E": "The application is allocating executable memory"
    },
    "SRWLock": {
        "0x250": "A thread tried to use SRW lock that is not initalized",
        "0x251": "The SRW lock is being re-initialized",
        "0x252": "The SRW lock is being released with a wrong release API",
        "0x253": "The SRW lock is being acquired recursively by the same thread",
        "0x254": "The thread that owns the SRW lock is exiting or being terminated",
        "0x255": "The SRW lock is being released by the thread that did not acquire the lock",
        "0x256": "The memory address being freed contains an active SRW lock that is still in use",
        "0x257": "The DLL being unloaded contains an active SRW lock that is still in use"
    },
    "Threadpool": {
        "0x700": "Thread priority is changed when thread is returned to threadpool",
        "0x701": "Thread affinity is changed when thread is returned to threadpool",
        "0x702": "One or more messages left as unprocessed when threadpool thread is returned to the threadpool",
        "0x703": "Any window is kept alive when threadpool thread is returned to the threadpool",
        "0x704": "ExitThread is called on a threadpool thread",
        "0x705": "Callback function changed the thread token to impersonate another user and forgot to reset it before "
        "returning it to the threadpool",
        "0x706": "Windows API that requires dedicated or persistent thread called from threadpool",
        "0x707": "Callback function forgot to close or reset the current transaction handle",
        "0x708": "Callback function called CoInit and CoUnInit in differing amounts (unbalanced)",
        "0x709": "The period to signal the timer is not zero when the timer is set to signal only once with the WT_EXECUTEONLYONCE flag",
        "0x70A": "The loader lock is held within the callback and is not released when the thread is returned to the threadpool",
        "0x70B": "The preferred language is set within the callback and is not cleared when the thread is returned to the threadpool",
        "0x70C": "The background priority is set within the callback and is not disabled when the thread is returned to the threadpool",
        "0x70D": "TerminateThread called on a threadpool thread",
    },
    "TLS": {
        "0x350": "A DLL that allocated a TLS index is being unloaded before freeing that TLS index",
        "0x351": "The internal verifier structures used to store the state of TLS slots for thread are corrupted",
        "0x352": "An invalid TLS index is used"
    }
}


def parseXML(filepath, dump_xml_on_error):
    xml_is_app_verifier = False
    app_verifier_entries = []

    print("Looking for AppVerifier XML file...")
    xml_tree = ElementTree.parse(filepath)

    # Go through every element in the XML tree
    for elem in xml_tree.iter():
        if (elem.tag == s_AppVerifier_LogText):
            xml_is_app_verifier = True
        elif (elem.tag == s_AppVerifier_EntryText):
            app_verifier_entries.append(elem)

    # If the XML does not have any AppVerifier data, then something went wrong!
    if (xml_is_app_verifier == False):
        print("ERROR: XML File from AppVerifier does not include a AppVerifier session!")
        return -1

    # If we have AppVerifier entries, then a test or tests failed, so process the data,
    # print it, and then return with an error to stop the GitHub action from passing
    if (len(app_verifier_entries) > 0):
        print("WARNING: AppVerifier entries found:")
        severity_error_found = False

        for entry in app_verifier_entries:
            element_time = entry.attrib.get("Time", "UNKNOWN")
            element_layer_name = entry.attrib.get("LayerName", "UNKNOWN")
            element_code = entry.attrib.get("StopCode", "UNKNOWN")
            element_severity = entry.attrib.get("Severity", "UNKNOWN")

            print_red = False
            if (element_severity in s_AppVerifier_ErrorSeverities):
                severity_error_found = True
                print_red = True

            if (print_red):
                print(
                    f"ERROR: [{element_time}] {element_severity.upper()} - Test: {element_layer_name} - Stop Code: {element_code}")
            else:
                print(
                    f"[{element_time}] {element_severity.upper()} - Test: {element_layer_name} - Stop Code: {element_code}")
            print(f"\t{getErrorCodeMeaning(element_layer_name, element_code)}")

        print(
            "\nNOTE: The error codes and information provided are just guesses based on the error code.\n"
            "\tRun AppVerifier locally and use WinDBG combined with the AppVerifier help to discover more "
            "about the error from its error code and how to debug it.")

        if (severity_error_found == True and dump_xml_on_error != None):
            if (dump_xml_on_error == True):
                print("\nERROR: Raw XML output for errors found:\n")
                for entry in app_verifier_entries:
                    print(ElementTree.tostring(
                        entry, encoding="unicode"))

        if (severity_error_found == True):
            print(
                "\nERROR: Failed due to AppVerifier finding entries marked as severe")
            return -1
        else:
            print("SUCCESS: AppVerifier entries were not marked as severe")
            return 0
    else:
        print("SUCCESS: No AppVerifier entries found! AppVerifier ran successfully and did not generate any entries")
        return 0


def getErrorCodeMeaning(element_layer_name, element_code):
    if (element_layer_name in s_AppVerifier_ErrorCodeHelp):
        layer_codes = s_AppVerifier_ErrorCodeHelp[element_layer_name]
        if (element_code in layer_codes):
            return layer_codes[element_code]
        else:
            return "Util-script unknown error: " + element_code + " for layer " + element_layer_name
    return "Util-script unknown layer: " + element_layer_name + " and error code: " + element_code


def booleanString(string):
    string = string.lower()
    if string not in {"false", "true"}:
        raise ValueError("Boolean is not true or false!")
    return string == "true"


def main():
    argument_parser = argparse.ArgumentParser(
        description="AppVerifier XML output util")

    argument_parser.add_argument("--xml_file", metavar="<C:\\example\\file.xml>",
                                 required=False, help="Path to XML file from AppVerifier")
    argument_parser.add_argument("--dump_xml_on_error", metavar="<True/False>", default=True, required=False,
                                 type=booleanString, help="If true, the XML for found issues will be printed to the console")

    parsed_commands = argument_parser.parse_args()

    print("\nStarting AppVerifier XML check...", flush=True)
    print(parsed_commands.dump_xml_on_error)
    xml_result = parseXML(parsed_commands.xml_file,
                            parsed_commands.dump_xml_on_error)
    print("\n")
    exit(xml_result)


if __name__ == "__main__":
    main()
