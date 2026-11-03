[app]
title = Cipher Glucose Control
package.name = cipherglucosecontrol
package.domain = mx.cipher
source.dir = .
source.include_exts = py,png,jpg,ttf,kv,json
source.exclude_dirs = .git,.github,bin,.buildozer
version = 4.3.0
requirements = python3,kivy,plyer
android.archs = arm64-v8a
orientation = portrait
fullscreen = 0
icon.filename = %(source.dir)s/icon.png
presplash.filename = %(source.dir)s/presplash.png
presplash.color = #F6F8F7
android.permissions = VIBRATE,POST_NOTIFICATIONS
android.api = 33
android.minapi = 21
android.sdk = 33
android.ndk = 25b
android.accept_sdk_license = True

[buildozer]
log_level = 2
warn_on_root = 0
