#!/usr/bin/env python3
"""Linux sampled, non-daemonizing process-group monitor; not a hard OS cap."""
from pathlib import Path
import json
import os
import shutil
import signal
import subprocess
import time


def available_bytes():
    return int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024


def group_members(pg):
    rows=[]
    for d in Path('/proc').iterdir():
        if not d.name.isdecimal(): continue
        try:
            st=(d/'stat').read_text().rsplit(')',1)[1].split()
            if int(st[2])==pg and st[0]!='Z': rows.append((int(d.name),int(st[21])*os.sysconf('SC_PAGE_SIZE')))
        except (FileNotFoundError,ProcessLookupError,PermissionError): pass
    return rows


def controller_rss_bytes():
    # The original Core replay cap included its Python controller. Count ours too.
    fields=Path('/proc/self/stat').read_text().rsplit(')',1)[1].split()
    return int(fields[21])*os.sysconf('SC_PAGE_SIZE')


def guarded_run(cmd,cwd,env,logs,name,profile):
    start=time.monotonic(); low=available_bytes(); peak=0; status='running'; signals=[]; p=None
    if low<profile['launch_available_bytes']: raise RuntimeError('Insufficient available host memory before launch')
    if shutil.disk_usage(cwd).free<profile['disk_launch_floor_bytes']: raise RuntimeError('Insufficient capture disk headroom')
    try:
        with (logs/(name+'.stdout.log')).open('x') as so, (logs/(name+'.stderr.log')).open('x') as se, (logs/(name+'.resources.jsonl')).open('x') as sf:
            p=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=so,stderr=se,start_new_session=True)
            while p.poll() is None:
                rss=sum(x[1] for x in group_members(p.pid))
                if profile.get('include_controller_rss',False): rss+=controller_rss_bytes()
                avail=available_bytes(); peak=max(peak,rss); low=min(low,avail)
                seconds=time.monotonic()-start
                sf.write(json.dumps({'seconds':seconds,'rss_bytes':rss,'available_bytes':avail})+'\n'); sf.flush()
                checks=[(rss>profile['rss_limit_bytes'],'rss_limit'),(avail<profile['host_floor_bytes'],'host_floor'),
                        (profile['wall_seconds'] is not None and seconds>profile['wall_seconds'],'wall_limit'),
                        (shutil.disk_usage(cwd).free<profile['disk_live_floor_bytes'],'disk_floor')]
                reason=next((reason for tripped,reason in checks if tripped),None)
                if reason:
                    status=reason; break
                time.sleep(profile['sample_seconds'])
    except BaseException:
        status='interrupted_or_error'; raise
    finally:
        if p is not None:
            if p.poll() is None or group_members(p.pid):
                for sig,delay in ((signal.SIGTERM,4),(signal.SIGKILL,2)):
                    if not group_members(p.pid): break
                    try: os.killpg(p.pid,sig); signals.append(sig.name)
                    except ProcessLookupError: pass
                    end=time.monotonic()+delay
                    while time.monotonic()<end and group_members(p.pid): p.poll(); time.sleep(.05)
                p.wait()
            remaining=group_members(p.pid); code=p.wait()
            if status=='running': status='passed' if code==0 and not remaining else 'failed'
            guard={'status':status,'exit_code':code,'seconds':time.monotonic()-start,'peak_sampled_group_rss_bytes':peak,
                   'minimum_available_bytes':low,'controller_rss_included':profile.get('include_controller_rss',False),'rss_limit_bytes':profile['rss_limit_bytes'],'host_floor_bytes':profile['host_floor_bytes'],
                   'signals':signals,'remaining_members':remaining,'scope':'Sampled non-daemonizing process-group monitor, not a hard OS cap'}
            (logs/(name+'.guard.json')).write_text(json.dumps(guard,indent=2)+'\n')
    return code,(logs/(name+'.stdout.log')).read_text(),(logs/(name+'.stderr.log')).read_text(),guard
