#!/usr/bin/env python

import datetime
import time
import sys


i = 0
while i < 20:
    tm = datetime.datetime.now().time()
    t = tm.strftime('%S/%M/%H')
    print (t)
    sys.stdout.flush()
    time.sleep(5)
    i = i + 1
