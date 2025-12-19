# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2024.06
# platform  : Linux 4.18.0-553.89.1.el8_10.x86_64
# version   : 2024.06p002 64 bits
# build date: 2024.09.02 16:28:38 UTC
# ----------------------------------------
# started   : 2025-12-19 15:45:03 EST
# hostname  : cadpc02.(none)
# pid       : 1690621
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:34727' '-style' 'windows' '-data' 'AAAAxHicVYvLCYBAEEPfCoLNaAUWoRWILAqCP/xdtVQ7WbOKhw1kkplJDJCfzjlemPtTckMIv0fhpbwChfgv/xFfSEhpmTnkCzYaBm2V2IkNvXSUVqz6LuxY6S7nb4fmokQrWmp9OiblMzmrrscDF8IZIQ==' '-proj' '/homes/user/stud/fall25/rm4305/6863-RISCV-FV/jgproject/sessionLogs/session_0' '-init' '-hidden' '/homes/user/stud/fall25/rm4305/6863-RISCV-FV/jgproject/.tmp/.initCmds.tcl' 'temp_pipeline_structure_verification.tcl'
# ----------------------------------------
#  Copyright (c) 2017 Cadence Design Systems, Inc. All Rights
#  Reserved.  Unpublished -- rights reserved under the copyright 
#  laws of the United States.
# ----------------------------------------

# Analyze design under verification files
set ROOT_PATH      ./
set RTL_PATH       ${ROOT_PATH}/src
set PROP_PATH      ${ROOT_PATH}/properties

# Analyze the complete RTL needed for bypass verification
set RTL_FILES [lsort [glob -nocomplain ${RTL_PATH}/*.v]]
if {[llength $RTL_FILES] == 0} {
  error "No RTL files found under ${RTL_PATH}"
}
analyze -sv $RTL_FILES

# Analyze property bindings (includes individual .sva files)
analyze -sva \
  ${PROP_PATH}/bind_pipeline_structure.sva
