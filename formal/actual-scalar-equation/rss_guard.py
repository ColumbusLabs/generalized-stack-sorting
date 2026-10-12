"""RSS watchdog for trusted, non-daemonizing commands in one new process group.

Sampled physical-RSS limit, not an OS hard cap. Every launched Lean/shell/Python
child inherits this group. This is not a sandbox for hostile session escapes.
The watchdog also terminates lingering children if the leader exits.
"""
import argparse
from datetime import datetime, timezone
import json, os
from pathlib import Path
import signal, subprocess, time

def members(group):
    rows=[]
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():continue
        try:
            raw=(p/'stat').read_text(); f=raw[raw.rfind(')')+2:].split()
            if int(f[2])==group and f[0]!='Z':
                rows.append({'pid':int(p.name),'rss':int(f[21])*os.sysconf('SC_PAGE_SIZE')})
        except (FileNotFoundError,ProcessLookupError,PermissionError):pass
    return rows

def available():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
    raise RuntimeError('No MemAvailable reading')

def teardown(p):
    signals=[]
    for sig,grace in [(signal.SIGTERM,1.0),(signal.SIGKILL,2.0)]:
        if not members(p.pid):break
        try:os.killpg(p.pid,sig);signals.append(sig.name)
        except ProcessLookupError:pass
        end=time.monotonic()+grace
        while time.monotonic()<end:
            p.poll()
            if not members(p.pid):break
            time.sleep(.02)
    p.wait()
    return signals,members(p.pid)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',required=True)
    ap.add_argument('--rss-limit',type=int,required=True)
    ap.add_argument('--host-floor',type=int,default=1610612736)
    ap.add_argument('command',nargs=argparse.REMAINDER)
    a=ap.parse_args();cmd=a.command[1:] if a.command[:1]==['--'] else a.command
    if not cmd or a.rss_limit<=0:raise ValueError('Invalid command or RSS limit')
    output=Path(a.output);output.mkdir(exist_ok=False)
    start=time.monotonic();status='starting';peak=0;low=available();p=None;clean=[];left=[]
    def interrupt(sig,frame):raise InterruptedError(str(sig))
    for sig in (signal.SIGTERM,signal.SIGINT,signal.SIGHUP):signal.signal(sig,interrupt)
    try:
        if low<a.host_floor:status='host-floor-before-start'
        else:
            with (output/'stdout.log').open('w') as out,(output/'stderr.log').open('w') as err,(output/'resources.jsonl').open('w') as log:
                p=subprocess.Popen(cmd,stdout=out,stderr=err,start_new_session=True)
                while True:
                    now=datetime.now(timezone.utc);rows=members(p.pid);rss=sum(x['rss'] for x in rows)
                    mem=available();peak=max(peak,rss);low=min(low,mem)
                    log.write(json.dumps({'utc':now.isoformat(),'rss_bytes':rss,'mem_available_bytes':mem,'pids':[x['pid'] for x in rows]})+'\n');log.flush()
                    code=p.poll()
                    if rss>a.rss_limit:status='rss-stop';break
                    if mem<a.host_floor:status='host-floor-stop';break
                    if now.year>2027:status='session-deadline';break
                    if code is not None:
                        status='passed' if code==0 else 'command-failed'
                        if rows:status='lingering-children'
                        break
                    time.sleep(.05)
    except BaseException as exc:
        status='interrupted-or-error:'+type(exc).__name__
    finally:
        if p is not None:clean,left=teardown(p)
        report={'status':status,'command':cmd,'seconds':time.monotonic()-start,
                'rss_limit_bytes':a.rss_limit,'host_floor_bytes':a.host_floor,
                'peak_sampled_group_rss_bytes':peak,'minimum_mem_available_bytes':low,
                'exit_code':None if p is None else p.returncode,'cleanup_signals':clean,
                'remaining_live_group_members':left,
                'scope':'Trusted non-daemonizing process group; sampled RSS, not hard OS cap'}
        (output/'result.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report,indent=2),flush=True)
    return 0 if status=='passed' and not left else 1

if __name__=='__main__':raise SystemExit(main())
