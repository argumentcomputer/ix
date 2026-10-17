#pragma once

// Keep the standalone BN254 registry and NTT singletons separate from other
// sppark instantiations that may be linked into the same process.
#define gpu_t ix_plonk_native_gpu_t
#define stream_t ix_plonk_native_stream_t
#define event_t ix_plonk_native_event_t
#define gpu_ptr_t ix_plonk_native_gpu_ptr_t
#define dev_ptr_t ix_plonk_native_dev_ptr_t
#define select_gpu ix_plonk_native_select_gpu
#define gpu_props ix_plonk_native_gpu_props
#define all_gpus ix_plonk_native_all_gpus
#define ngpus ix_plonk_native_ngpus
#define cuda_available ix_plonk_native_cuda_available
#define drop_gpu_ptr_t ix_plonk_native_drop_gpu_ptr_t
#define clone_gpu_ptr_t ix_plonk_native_clone_gpu_ptr_t
#define drop_error_message ix_plonk_native_drop_error_message
#define sppark_error ix_plonk_native_sppark_error
#define cuda_error ix_plonk_native_cuda_error
#define NTT IxPlonkNativeNTT
#define NTTParameters IxPlonkNativeNTTParameters
#define CT_launcher IxPlonkNativeCTLauncher
#define GS_launcher IxPlonkNativeGSLauncher
