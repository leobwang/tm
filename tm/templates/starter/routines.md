<!--
routines.md — open recurring windows. Every line has a window (`win:` + `dur:`)
or an `after-done:` interval, and ci defaults to 1. There is no checkbox here:
instances live in the log (`tm routine done <name>`, `tm skip <name>`), so the
line itself never changes. A missed window expires unless you say
`on-miss:persist`.

    - sleep      win:22:00-08:00 dur:8h30m every:day ci:0
    - breakfast  win:06:00-09:00 dur:30m  every:day pref:wake+10m
    - lunch      win:11:30-13:30 dur:30m  every:day
    - workout    win:16:00-19:00 dur:1h   every:Mon,Wed,Fri
    - shower     win:07:00-23:00 dur:20m  after-done:2d~1d
    - laundry    win:09:00-21:00 dur:30m  every:week on-miss:persist
-->
