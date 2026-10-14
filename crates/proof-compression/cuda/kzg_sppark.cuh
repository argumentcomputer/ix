#pragma once

// Goldilocks links sppark without its C++ thread pool. Its gpu_t layout and
// field-specific NTT singletons must not alias this instantiation's symbols.
#define gpu_t kzg_gpu_t
#define gpus_t kzg_gpus_t
#define stream_t kzg_stream_t
#define event_t kzg_event_t
#define gpu_ptr_t kzg_gpu_ptr_t
#define dev_ptr_t kzg_dev_ptr_t
#define select_gpu kzg_select_gpu
#define gpu_props kzg_gpu_props
#define all_gpus kzg_all_gpus
#define ngpus kzg_ngpus
#define cuda_available kzg_cuda_available
#define drop_gpu_ptr_t kzg_drop_gpu_ptr_t
#define clone_gpu_ptr_t kzg_clone_gpu_ptr_t
#define drop_error_message kzg_drop_error_message
#define sppark_error kzg_sppark_error
#define cuda_error kzg_cuda_error
#define NTT KzgNTT
#define NTTParameters KzgNTTParameters
#define CT_launcher KzgCTLauncher
#define GS_launcher KzgGSLauncher
