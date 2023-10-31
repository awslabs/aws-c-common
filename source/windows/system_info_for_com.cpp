/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <windows.h>
#include <Wbemidl.h>
#include <comdef.h>

#include <aws/common/private/system_info_priv.h>

#include <aws/common/byte_buf.h>
#include <aws/common/logging.h>
#include <aws/common/thread.h>
#include <aws/common/stdint.h>

#include <inttypes.h>

int aws_system_environment_load_platform_impl(struct aws_system_environment *env) {
    struct aws_allocator *allocator = env->allocator;
    HRESULT hres;
    IWbemLocator *p_loc = NULL;
    IWbemServices *p_svc = NULL;
    IEnumWbemClassObject *p_enumerator = NULL;
    IWbemClassObject *p_cls_obj = NULL;
    VARIANT vt_prop;
    ULONG u_return;
    int result = AWS_OP_SUCCESS;

    /* Initialize COM. */
    hres = CoInitializeEx(0, COINIT_MULTITHREADED);
    if (FAILED(hres)) {
        AWS_LOGF_WARN(AWS_LS_COMMON_GENERAL, "Failed to initialize COM library. Error code = %" PRIx32, hres);
        return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
    }

    /* Initialize COM security. */
    hres = CoInitializeSecurity(
        NULL, -1, NULL, NULL, RPC_C_AUTHN_LEVEL_DEFAULT, RPC_C_IMP_LEVEL_IMPERSONATE, NULL, EOAC_NONE, NULL);
    if (FAILED(hres)) {
        AWS_LOGF_WARN(
            AWS_LS_COMMON_GENERAL, "Failed to initialize COM library security policy. Error code = %" PRIx32, hres);
        result = aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
        goto cleanup_com;
    }

    /* Create WMI COM instance. */
    hres = CoCreateInstance(CLSID_WbemLocator, 0, CLSCTX_INPROC_SERVER, IID_IWbemLocator, (LPVOID *)&p_loc);
    if (FAILED(hres)) {
        AWS_LOGF_WARN(AWS_LS_COMMON_GENERAL, "Failed to load WMI COM component. Error code = %" PRIx32, hres);
        result = aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
        goto cleanup_com;
    }

    /* Connect to WMI. */
    hres = p_loc->ConnectServer(_bstr_t(L"ROOT\\CIMV2"), NULL, NULL, 0, NULL, 0, 0, &p_svc);
    if (FAILED(hres)) {
        AWS_LOGF_WARN(AWS_LS_COMMON_GENERAL, "Failed to connect to WMI COM component. Error code = %" PRIx32, hres);
        result = aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
        goto cleanup_wmi_locator;
    }

    AWS_LOGF_DEBUG(AWS_LS_COMMON_GENERAL, "Connected to ROOT\\CIMV2 WMI namespace");

    /* Set COM proxy blanket. */
    hres = CoSetProxyBlanket(
        p_svc,
        RPC_C_AUTHN_WINNT,
        RPC_C_AUTHZ_NONE,
        NULL,
        RPC_C_AUTHN_LEVEL_CALL,
        RPC_C_IMP_LEVEL_IMPERSONATE,
        NULL,
        EOAC_NONE);
    if (FAILED(hres)) {
        AWS_LOGF_WARN(
            AWS_LS_COMMON_GENERAL, "Failed to set proxy blanket on WMI COM component. Error code = %" PRIx32, hres);
        result = aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
        goto cleanup_wmi_services;
    }

    /* Execute query to get manufacturer and product name. */
    hres = p_svc->ExecQuery(
        bstr_t("WQL"),
        bstr_t("SELECT * FROM Win32_ComputerSystem"),
        WBEM_FLAG_FORWARD_ONLY | WBEM_FLAG_RETURN_IMMEDIATELY,
        NULL,
        &p_enumerator);
    if (FAILED(hres)) {
        AWS_LOGF_WARN(AWS_LS_COMMON_GENERAL, "Failed to query WMI COM component. Error code = %" PRIx32, hres);
        result = aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
        goto cleanup_wmi_services;
    }

    while (p_enumerator) {
        hres = p_enumerator->Next(WBEM_INFINITE, 1, &p_cls_obj, &u_return);
        if (0 == u_return) {
            break;
        }

        /* Get Manufacturer property. */
        hres = p_cls_obj->Get(L"Manufacturer", 0, &vt_prop, 0, 0);
        if (SUCCEEDED(hres)) {
            struct aws_string *mb_manufacturer_val = aws_string_convert_from_wchar_c_str(allocator, vt_prop.bstrVal);
            aws_byte_buf_init(&env->virtualization_vendor, allocator, mb_manufacturer_val->len);
            aws_byte_buf_write_from_whole_string(&env->virtualization_vendor, mb_manufacturer_val);
            aws_string_destroy(mb_manufacturer_val);
            AWS_LOGF_DEBUG(
                AWS_LS_COMMON_GENERAL,
                "Loaded virtualization vendor from WMI as " PRInSTR,
                AWS_BYTE_BUF_PRI(env->virtualization_vendor));
        }
        VariantClear(&vt_prop);

        /* Get Model property. */
        hres = p_cls_obj->Get(L"Model", 0, &vt_prop, 0, 0);
        if (SUCCEEDED(hres)) {
            struct aws_string *mb_model_val = aws_string_convert_from_wchar_c_str(allocator, vt_prop.bstrVal);
            aws_byte_buf_init(&env->product_name, allocator, mb_model_val->len);
            aws_byte_buf_write_from_whole_string(&env->product_name, mb_model_val);
            aws_string_destroy(mb_model_val);
            AWS_LOGF_DEBUG(
                AWS_LS_COMMON_GENERAL,
                "Loaded virtualization product name from WMI as " PRInSTR,
                AWS_BYTE_BUF_PRI(env->product_name));
        }
        VariantClear(&vt_prop);

        p_cls_obj->Release();
        p_cls_obj = NULL;
    }

    /* Cleanup enumerator for the next query */
    if (p_enumerator) {
        p_enumerator->Release();
        p_enumerator = NULL;
    }

    /* Query for network devices */
    hres = p_svc->ExecQuery(
        bstr_t("WQL"),
        bstr_t("SELECT * FROM Win32_NetworkAdapter WHERE NetEnabled = true"),
        WBEM_FLAG_FORWARD_ONLY | WBEM_FLAG_RETURN_IMMEDIATELY,
        NULL,
        &p_enumerator);

    if (FAILED(hres)) {
        AWS_LOGF_WARN(AWS_LS_COMMON_GENERAL, "Failed to query network devices. Error code = %" PRIx32, hres);
        result = aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
        goto cleanup_wmi_services;
    }

    uint16_t numa_nodes = aws_get_cpu_group_count();
    uint16_t counter = 0;
    /* loop over network devices */
    while (p_enumerator) {
        HRESULT hr = p_enumerator->Next(WBEM_INFINITE, 1, &p_cls_obj, &u_return);

        if (0 == u_return) {
            break;
        }

        /* Get the value of the Manufacturer property. */
        hr = p_cls_obj->Get(L"Name", 0, &vt_prop, 0, 0);
        if (SUCCEEDED(hr)) {
            struct aws_string *mb_nic_name = aws_string_convert_from_wchar_c_str(allocator, vt_prop.bstrVal);
            aws_array_list_push_back(&env->str_list_network_cards, &mb_nic_name);
            /* currently just spread them around, as we don't know how to get the node for a network device.
               Tried WMI, but there's no such property we can find. Also, don't trust ChatGPT on this as it
               is wrong. */
            uint16_t node_for_nic = counter++ % numa_nodes;
            aws_array_list_push_back(&env->u16_nic_to_cpu_group, &node_for_nic);            
        }

        p_cls_obj->Release();
        p_cls_obj = NULL;
    }

    /* Cleanup enumerator for the next query */
    if (p_enumerator) {
        p_enumerator->Release();
        p_enumerator = NULL;
    }    

cleanup_wmi_services:
    if (p_svc) {
        p_svc->Release();
        p_svc = NULL;
    }

cleanup_wmi_locator:
    if (p_loc) {
        p_loc->Release();
        p_loc = NULL;
    }

cleanup_com:
    CoUninitialize();
    return result;
}

void aws_system_environment_destroy_platform_impl(struct aws_system_environment *env) {
    size_t length = aws_array_list_length(&env->str_list_network_cards);

    for (size_t i = 0; i < length; ++i) {
        struct aws_string *device_name = NULL;
        aws_array_list_get_at(&env->str_list_network_cards, &device_name, i);
        aws_string_destroy(device_name);
    }

    aws_byte_buf_clean_up(&env->virtualization_vendor);
    aws_byte_buf_clean_up(&env->product_name);
}
