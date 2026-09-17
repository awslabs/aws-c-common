# Reads VERSION file (format: MAJOR.MINOR.PATCH) and derives:
#   var_version_simple  - "MAJOR.MINOR.PATCH"
#   var_version_soname  - "MAJOR.MINOR" (for use as SOVERSION)
function(aws_get_version var_version_simple var_version_soname)
    file(READ "${CMAKE_CURRENT_SOURCE_DIR}/VERSION" version_simple)
    string(STRIP "${version_simple}" version_simple)
    set(${var_version_simple} ${version_simple} PARENT_SCOPE)

    string(REPLACE "." ";" version_list ${version_simple})
    list(GET version_list 0 version_major)
    list(GET version_list 1 version_minor)
    set(${var_version_soname} "${version_major}.${version_minor}" PARENT_SCOPE)
endfunction()
