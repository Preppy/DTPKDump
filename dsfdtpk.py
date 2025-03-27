# =====================================================================================================
# Preliminary DTPK--->DSF converter (ver 0.01 2008-11-02) by kingshriek
# This script only supports the AM2 DTPK sound driver and not necessarily all the different versions 
# of it.
# The script is set up by default to ignore sound effect data and only process actual sequenced music.
# Updated by Preppy 2024 for a couple minor nits
# Update history located near end of file
# =====================================================================================================

# =====================================================================================================
import os
import sys
import zlib
from struct import pack,unpack 
from array import array
from glob import glob
from copy import copy
# =====================================================================================================

# =====================================================================================================
# Convert RAM image to DSF format
def bin2dsf(nout, dsfbin, load=0, tagdict={}):
    dsfz = zlib.compress(array('B', pack('<I', load)) + dsfbin)
    sig = 'PSF' + '\x12'
    res = pack('<I', 0)
    size = pack('<I', len(dsfz))
    crc = pack('<I', zlib.crc32(dsfz))
    if tagdict:
        tag = '[TAG]'
        for field in tagdict:
            tag += '%s=%s\x0A' % (field, tagdict[field])
    else:
        tag = ''
    open(nout, 'wb').write(bytes(sig, "utf8") + res + size + crc + dsfz + bytes(tag, "utf8"))

# ====================================================================================================

# =====================================================================================================
# Create dsf using DTPK file
def dsfdtpk(nout,ndrv,ndtpk,track=None,doall=False,alldsf=False,allminidsf=False):
	# Read in driver file
	dsfbin = array('B', [0] * 0x10000)
	ddrv = array('B', open(ndrv, 'rb').read())
	szdrv = len(ddrv)
	dsfbin[0:szdrv] = ddrv

	# Read in DTPK file
	ddtpk = array('B', open(ndtpk, 'rb').read())

	# Python 3.2 deprecated tostring
	if sys.version_info[0] >= 3 and sys.version_info[1] >= 2:
		if ddtpk[:4].tobytes() != b'DTPK':
			print ('Skipping %s - not a valid DTPK sound file' % ndtpk )
			return
	else:
		if ddtpk[:4].tostring() != 'DTPK':
			print ('Skipping %s - not a valid DTPK sound file' % ndtpk )
			return

	dsfbin += ddtpk

	# Configure driver for either Dreamcast or Naomi
	if len(dsfbin) > 0x1FE000:
		dsfbin[0x50:0x54] = array('B', pack('<I', 0x200))    # set driver config to Naomi if > than 2 MB needed

	# Set up sound map
	bank = 0
	dtpk_id = unpack('<I', ddtpk[4:8])[0]
	dsfbin[0x60+bank*4:0x64+bank*4] = array('B', pack('<I', dtpk_id))   # Map bank to DTPK id

	# Determine bank command
	bank_cmd = 0xA0001100 | bank

	# Determine sequence command(s)
	seq_offset = seq_offset_start = unpack('<I', ddtpk[0x2C:0x30])[0]
	if not seq_offset:
		print ('Skipping %s - no sequence data found' % ndtpk)
		return

	ncmds = unpack('<I', ddtpk[seq_offset:seq_offset+4])[0] + 1
	seq_cmds = []
	seq_count_offset = []
	seq_offset += 4
	for icmd in range(ncmds):
		seq_cmds.append(unpack('<I', ddtpk[seq_offset:seq_offset+4])[0] & 0xFFFF0000)
		seq_count_offset.append(unpack('<I', ddtpk[seq_offset:seq_offset+4])[0] & 0xFFFF)
		seq_offset += 4

	# Skip processing if sound effects/other data detected and user doesn't want them
	if not doall and all([(seq_cmd>>24) != 0xA8 for seq_cmd in seq_cmds]):
		print ('Skipping %s - sound effects or other data' % ndtpk)
		return

	for seq_cmd in seq_cmds:
		if track:
			seq_cmd |= (track << 8)

		# Write sound commands
		cmd_offset = 0x400
		dsfbin[0x400:0x404] = array('B', pack('>I', bank_cmd))    # Register DTPK bank
		if doall or (seq_cmd>>24) == 0xA8:
			dsfbin[0x404:0x408] = array('B', pack('>I', seq_cmd))     # Play sequence

	# Get number of tracks per group
	track_counts = [0x00] * ncmds
	for igroup in range(ncmds):
		track_counts[igroup] = unpack('<I', ddtpk[seq_offset_start + seq_count_offset[igroup]:seq_offset_start + seq_count_offset[igroup] +4])[0] + 1
		seq_offset += 4

	print ('Converting %s...' % ndtpk)

	# Allsdf songs extraction
	if alldsf:
		(xout, eout) = os.path.splitext(nout)
		for icmd, seq_cmd in enumerate(seq_cmds):
			if not doall and (seq_cmd >> 24) != 0xA8:
				continue
			for itrack in range(track_counts[icmd]):
				new_seq_cmd = (seq_cmd & 0xFFFF0000) | (itrack << 8)  # Create a new command for each track
				fout = f'{xout}_{icmd:02d}_{itrack:02d}.dsf'
				print(f'\tCreating {fout} (bank_cmd {bank_cmd:08X} seq_cmd {new_seq_cmd:08X})')
				dsfbin[0x404:0x408] = array('B', pack('>I', new_seq_cmd))  # Update sequence command
				bin2dsf(fout, dsfbin)

	if not alldsf or allminidsf:
		# Create DSF or miniDSFs based on number of tracks
		if not allminidsf and len(seq_cmds) == 1 and track_counts[0] == 1 or track is not None :
			seq_cmd = seq_cmds[0]
			print(f'\tCreating {nout} (bank_cmd {bank_cmd:08X} seq_cmd {seq_cmd:08X})')
			bin2dsf(nout, dsfbin)
		else:
			(xout, eout) = os.path.splitext(nout)
			fout = f'{xout}.dsflib'
			print(f'\tCreating {fout}')
			bin2dsf(fout, dsfbin)

			tagdict = {'_lib': fout}  # Tag data that points minidsfs to the dsflib
			for icmd, seq_cmd in enumerate(seq_cmds):
				if not doall and (seq_cmd >> 24) != 0xA8:
					continue
				for itrack in range(track_counts[icmd]):
					new_seq_cmd = (seq_cmd & 0xFFFF0000) | (itrack << 8)  # Include track number in sequence command
					trackbin = array('B', pack('>I', new_seq_cmd))
					load = 0x404
					fout = f'{xout}_{icmd:02d}_{itrack:02d}.minidsf'
					print(f'\tCreating {nout} (bank_cmd {bank_cmd:08X} seq_cmd {new_seq_cmd:08X})')
					bin2dsf(fout, trackbin, load, tagdict)
# =====================================================================================================

# =====================================================================================================
if __name__ == '__main__':
	argv = sys.argv
	argc = len(argv)
	default_flags = {'a':0, 't':0, 'd':0, 'm':0}
	default_params = {'track': None, 'doall': False,'alldsf': False,'allminidsf': False}
	if argc < 3:
		print ('AM2 DTPK DSF script v0.03 by kingshriek')
		print ('Usage: python %s <DTPK sound driver> [options] <DTPK sound files...>' % argv[0])
		print ('Options:')
		print ('          -a       include sound effects and other sound data')
		print ('          -d       create dsf regardless')
		print ('          -m       create minidsf regardless')
		print ('          -t <n>   disable automatic minidsf creation and create a single dsf with specified track number')
		print ('          --       turn all previous flags off')
		sys.exit(0)

	ndrv = argv[1]

	flags = copy(default_flags)
	params = copy(default_params)

	count_options = 0

	for arg in argv[2:]:

		if flags['a']:
			params['doall'] = True
			flags['a'] = 0

		if flags['d']:
			params['alldsf'] = True
			flags['d'] = 0

		if flags['m']:
			params['allminidsf'] = True
			flags['m'] = 0

		if flags['t']:
			params['track'] = int(arg)
			flags['t'] = 0
			continue

		if arg[0] == '-':
			flag = arg[1:]
			if flag in flags:
				flags[flag] = 1
			elif flag == '-':
				flags = copy(default_flags)
				params = copy(default_params)
			else:
				print ('Error: Invalid option -%s' % flag)
				sys.exit(1)
		else:
			ndtpks = glob(arg)

			if (len(ndtpks) == 0):
				print('Error: DTPK file not found.')
				sys.exit(1)

			for ndtpk in ndtpks:
				(xdtpk, edtpk) = os.path.splitext(ndtpk)
				nout = xdtpk + '.dsf'
				dsfdtpk(nout,ndrv,ndtpk,**params)

# =====================================================================================================

# =====================================================================================================
# 24-06-16 (0.03) - Force DSF/miniDSF extraction with -d/-m arguments
# 24-06-12 (0.02) - Support Python 3.x, improve handling of track count
# 08-11-02 (0.01) - Fixed script so that it pulls BGM from hybrid sound files (w/ mixed commands) with
#                   default settings (it would previously skip the file).
# 08-10-31 (0.00) - Initial version.
# =====================================================================================================