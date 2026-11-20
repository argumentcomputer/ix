import threading, sys
def main():
    import sim
    for f in ['hidden','outputs','transpose11x16','transpose20x16','transpose20x11','update_row16','update_w2','update_bias16']:
        bs, fs, lk = sim.path(f); print(f, len(bs), len(fs), lk, [n for n,_ in fs][:6])
t = threading.Thread(target=main); t.start(); t.join()
