//go:build !bls12381 && cuda

package cuda

import (
	"encoding/json"
	"fmt"
	"os"
	"time"
)

func (a *Accelerator) traceEvent(event, operation string, fields map[string]any) {
	if !a.trace {
		return
	}
	fields["kind"], fields["event"], fields["operation"] = "plonk_cuda_callback", event, operation
	fields["time"] = time.Now().UTC().Format(time.RFC3339Nano)
	if encoded, err := json.Marshal(fields); err == nil {
		fmt.Fprintln(os.Stderr, string(encoded))
	}
}

// Callback snapshots run while the accelerator lock and OS-thread lease are held.
type transferTrace struct {
	before  Stats
	err     error
	enabled bool
}

func (a *Accelerator) startTransferTrace(context *nativeContext) transferTrace {
	if !a.trace {
		return transferTrace{}
	}
	before, err := context.stats()
	return transferTrace{before: before, err: err, enabled: true}
}

func (trace transferTrace) finish(context *nativeContext, fields map[string]any) {
	if !trace.enabled {
		return
	}
	if trace.err != nil {
		fields["transfer_stats_error"] = trace.err.Error()
		return
	}
	after, err := context.stats()
	if err != nil {
		fields["transfer_stats_error"] = err.Error()
		return
	}
	fields["native_transfers"] = map[string]any{
		"dma_timing_enabled":             after.TransferTimingEnabled,
		"wall_includes_predecessor_work": true,
		"upload_dma_ms":                  after.UploadDMAMS - trace.before.UploadDMAMS,
		"download_dma_ms":                after.DownloadDMAMS - trace.before.DownloadDMAMS,
		"upload_bytes":                   after.UploadBytes - trace.before.UploadBytes,
		"download_bytes":                 after.DownloadBytes - trace.before.DownloadBytes,
		"upload_calls":                   after.UploadCalls - trace.before.UploadCalls,
		"download_calls":                 after.DownloadCalls - trace.before.DownloadCalls,
		"upload_wall_ms":                 after.UploadWallMS - trace.before.UploadWallMS,
		"download_wall_ms":               after.DownloadWallMS - trace.before.DownloadWallMS,
		"host_copy_ms_nested":            after.TransferHostCopyMS - trace.before.TransferHostCopyMS,
	}
}
