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

# Elaborate the full core so both decode and stall units are instantiated
elaborate -top RISC_V_Core

# Set up Clocks and Resets
clock -none
reset -none

# Get design information to check general complexity
get_design_info

# Prove properties
prove -all

# Report proof results
report
