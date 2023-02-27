" Vim ftplugin file
" Language:	MiniTT
" Maintainer: Oleg Grenrus <oleg.grenrus@iki.fi>
if exists('b:poritt_ftplugin')
	finish
endif
let b:poritt_ftplugin = 1

" almost everything is ok in keywords
setlocal iskeyword=a-z,A-Z,48-57,-,.,>,<,:,*,=,\\,\,,`

" comments start with --
setlocal commentstring=--\ %s
