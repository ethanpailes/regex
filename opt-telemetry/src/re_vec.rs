// generated by mk_regex_vec.sh
use regex::bytes::Regex;
use regex::Error;
use util::regex;

pub fn re_vec() -> Vec<Result<Regex, Error>> {
vec![
regex(r"/"),
regex(r"^u([0-9]+)(be|le|he)?$"),
regex(r"^[A-Z]{2}\d{2}[A-Z\d]{1,30}$"),
regex(r".*\[(?P<percent>.+)%.*\].*"),
regex(r"(.+?)(\[.*?\])?"),
regex(r":(?P<k>[a-zA-Z_]+)"),
regex(r"^\d{6}(?:\s*,\s*\d{6})*$"),
regex(r"^[jxe.uidchtnbpygk]{32,48}$"),
regex(r"^[cbdefghijklnrtuv]{32,48}$"),
regex(r"[\\/]([^\\/?]+)(\?.*)?$"),
regex(r"^pub use (ffi(::.+)*)::\*;$"),
regex(r"\bc_char\b"),
regex(r"\bc_void\b"),
regex("\"[a-z]*\":null"),
regex(",+"),
regex(",\\}"),
regex("\\{,"),
regex(r"[a-zA-Z_\$][a-zA-Z_0-9]*"),
regex(r"thi[sng]+"),
regex(r"(.+)\s+\((.+?)\)"),
regex(r"([\d\.]+)\s*out\s*of\s*([\d\.]+)"),
regex(r"^([\d\.]+)\s*(?:\(\))?$"),
regex(r"([\d\.]+)\s*Points\s*Possible"),
regex(r"([\d\.]+)\s*/\s*([\d\.]+)"),
regex(r"[^a-z0-9-]+"),
regex(r"[0-9]{14}_[a-z0-9-]+"),
regex(r"([0-9]{14}_)?[a-z0-9-]+"),
regex(r">\s+<"),
regex(r"\s{2,}|[\r\n]"),
regex(r"<(style|script)[\w|\s].*?>"),
regex("<!--(.|\n)*?-->"),
regex(r"<\w.*?>"),
regex(r" \s+|\s +"),
regex(r"\w\s+\w"),
regex(r"'\s+>"),
regex(r"\d\s+>"),
regex(r"(?P<relation>\([^)]+\))|(?P<prop>[a-zA-Z0-9_]+)"),
regex(r"\((.*)\)."),
regex("[A-Za-z0-9_]"),
regex(r"(\d+)x(\d+)"),
regex(r"(?P<nmsg>\d+) (?P<size>\d+)"),
regex(r"(?P<msgid>\d+) (?P<uidl>[\x21-\x7E]{1,70})"),
regex(r"(<.*>)\r\n$"),
regex(r"^(?P<status>\+OK|-ERR) (?P<statustext>.*)"),
regex(r"^\.\r\n$"),
regex(r"\+OK(.*)"),
regex(r"-ERR(.*)"),
regex(r"\+OK (\d+) (\d+)\r\n"),
regex(r"(\d+) ([\x21-\x7e]+)\r\n"),
regex(r"\+OK (\d+) ([\x21-\x7e]+)\r\n"),
regex(r"(\d+) (\d+)\r\n"),
regex(r"\+OK (\d+) (\d+)\r\n"),
regex("github:(\\w+)/?(\\w+)?"),
regex("^[0-9]{5}"),
regex(r"((?:(?:0|1[\d]{0,2}|2(?:[0-4]\d?|5[0-5]?|[6-9])?|[3-9]\d?)\.){3}(?:0|1[\d]{0,2}|2(?:[0-4]\d?|5[0-5]?|[6-9])?|[3-9]\d?))"),
regex(r"((([0-9A-Fa-f]{1,4}:){7}[0-9A-Fa-f]{1,4})|(([0-9A-Fa-f]{1,4}:){6}:[0-9A-Fa-f]{1,4})|(([0-9A-Fa-f]{1,4}:){5}:([0-9A-Fa-f]{1,4}:)?[0-9A-Fa-f]{1,4})|(([0-9A-Fa-f]{1,4}:){4}:([0-9A-Fa-f]{1,4}:){0,2}[0-9A-Fa-f]{1,4})|(([0-9A-Fa-f]{1,4}:){3}:([0-9A-Fa-f]{1,4}:){0,3}[0-9A-Fa-f]{1,4})|(([0-9A-Fa-f]{1,4}:){2}:([0-9A-Fa-f]{1,4}:){0,4}[0-9A-Fa-f]{1,4})|(([0-9A-Fa-f]{1,4}:){6}((\d((25[0-5])|(1\d{2})|(2[0-4]\d)|(\d{1,2}))\d)\.){3}(\d((25[0-5])|(1\d{2})|(2[0-4]\d)|(\d{1,2}))\d))|(([0-9A-Fa-f]{1,4}:){0,5}:((\d((25[0-5])|(1\d{2})|(2[0-4]\d)|(\d{1,2}))\d)\.){3}(\d((25[0-5])|(1\d{2})|(2[0-4]\d)|(\d{1,2}))\d))|(::([0-9A-Fa-f]{1,4}:){0,5}((\d((25[0-5])|(1\d{2})|(2[0-4]\d)|(\d{1,2}))\d)\.){3}(\d((25[0-5])|(1\d{2})|(2[0-4]\d)|(\d{1,2}))\d))|([0-9A-Fa-f]{1,4}::([0-9A-Fa-f]{1,4}:){0,5}[0-9A-Fa-f]{1,4})|(::([0-9A-Fa-f]{1,4}:){0,6}[0-9A-Fa-f]{1,4})|(([0-9A-Fa-f]{1,4}:){1,7}:))"),
regex(r"<value><string>([0-9.]*)</string></value>"),
regex(r"<int>([0-9]+)</int>"),
regex(r"<int>([0-9]+)</int>"),
regex(r"<boolean>([0-1]*)</boolean>"),
regex(r"(\d*)\.(\d*)\.(\d*)(-(\S*))?"),
regex(r"^(\S*) (\d*)\.(\d*)\.(\d*)(-(\S*))?"),
regex(r"arch/([a-z0-9_])+/"),
regex(r"arch/([a-z0-9_])+/"),
regex(r"^\s*((\*(/\d+)?)|[0-9-,/]+)(\s+((\*(/\d+)?)|[0-9-,/]+)){4,5}\s*$"),
regex(r"^/sys/.*?/gpio/gpio(\d+)$"),
regex("__?hidden#\\d+_"),
regex(r"^Linux ([^ ]+) (.*) \w+(?: GNU/Linux)?$"),
regex("^(?u:\""),
regex("^(?u:\\#)(?u:[\t-\r - \u{85}-\u{85}\u{a0}-\u{a0}\u{1680}-\u{1680}\u{2000}-\u{200a}\u{2028}-\u{2029}\u{202f}-\u{202f}\u{205f}-\u{205f}\u{3000}-\u{3000}])*(?u:.)+"),
regex("^(?u:=)(?u:[\t-\r - \u{85}-\u{85}\u{a0}-\u{a0}\u{1680}-\u{1680}\u{2000}-\u{200a}\u{2028}-\u{2029}\u{202f}-\u{202f}\u{205f}-\u{205f}\u{3000}-\u{3000}])*(?u:.)+"),
regex("^(?u:[A-Z_-_a-z])(?u:[0-9A-Z_-_a-z])*"),
regex("^(?u:!)"),
regex("^(?u:\\()"),
regex("^(?u:\\))"),
regex("^(?u:,)"),
regex("^(?u::)"),
regex("^(?u:@)"),
regex("^(?u:\\[)"),
regex("^(?u:\\])"),
regex("^(?u:enum)"),
regex("^(?u:implements)"),
regex("^(?u:input)"),
regex("^(?u:interface)"),
regex("^(?u:scalar)"),
regex("^(?u:type)"),
regex("^(?u:union)"),
regex("^(?u:\\{)"),
regex("^(?u:\\})"),
regex(r"[\d]+(?:[~\x{2053}\x{223C}\x{FF5E}][\d]+)?"),
regex(r"[, \[\]]"),
regex(r"[\\/] *x"),
regex(r"[[\P{N}&&\P{L}]&&[^#]]+$"),
regex(r"(?:.*?[A-Za-z]){3}.*"),
regex(r"(\D+)"),
regex(r"(\$\d)"),
regex(r"\(?\$1\)?"),
regex(r"\D"),
regex(r"^0+"),
regex(r"^89"),
regex(r"^8+"),
regex(r"^ *(\^_*\^) *$"),
regex(r"^[_\p{XID_Start}]$"),
regex(r"^\p{XID_Continue}$"),
regex("%25(?P<hex>[0-9a-fA-F][0-9a-fA-F])"),
regex("^package://(\\w+)/"),
regex(r"hello world"),
regex("^(?:(?:(?:\\d+:).+)|(?:[^:]+))$"),
regex(r"(?:[Cc]opyright|©)(?:\s|[©:,()Cc<])*\b\d{4}\b.*$"),
regex(r"^.*\.h$"),
regex(r"^.*\.c$"),
regex(r"^.*\.hpp$"),
regex(r"^.*\.cc$"),
regex(r"^.*\.cpp$"),
regex(r"CPtr\(\w+\)"),
regex(r"^Version:\s(\d\.\d\.\d)\sFeatures:\s+(\w+)?\sMode:\s(\w+)$"),
regex(r"RawDatabase<Block>\{db: \w+\}"),
regex(r"RawSerializedDatabase\{p: \w+, len: \d+\}"),
regex(r".*"),
regex(r".*"),
regex(r".*"),
regex(r".*"),
regex(r".*"),
regex(r".*"),
regex(r"^[a-z]+$"),
regex(r"^[a-z]+$"),
regex(r"(\.git|\.pijul|_darcs|\.hg)$"),
regex(r".*?\.(a|la|lo|o|ll|keter|bc|dyn_o|d|rlib|crate|min\.js|hi|dyn_hi|S|jsexe|webapp|js\.externs|ibc|toc|aux|fdb_latexmk|fls|egg-info|whl|js_a|js_hi|jld|ji|js_o|so.*|dump-.*|vmb|crx|orig|elmo|elmi|pyc|mod|p_hi|p_o|prof|tix)$"),
regex(r".*?\.(stats|conf|h|out|cache.*|dat|pc|info|\.js)$"),
regex(r".*?\.(exe|a|la|o|ll|keter|bc|dyn_o|d|rlib|crate|min\.js|hi|dyn_hi|jsexe|webapp|js\.externs|ibc|toc|aux|fdb_latexmk|fls|egg-info|whl|js_a|js_hi|jld|ji|js_o|so.*|dump-.*|vmb|crx|orig|elmo|elmi|pyc|mod|p_hi|p_o|prof|tix)$"),
regex(r".*?\.(stats|conf|h|out|cache.*|\.js)$"),
regex(r"(\.git|\.pijul|_darcs|\.hg)$"),
regex(r".*?\.(dyn_o|out|d|hi|dyn_hi|dump-.*|p_hi|p_o|prof|tix)$"),
regex(r".*?\.(ibc)$"),
regex(r"\.stack-work|dist-newstyle"),
regex(r"_NET_WM_PID\(CARDINAL\) = (\d+)"),
regex(r"today|yesterday|now"),
regex(r"(?P<day>\d{1,2})/(?P<month>\d{1,2})(/(?P<year>\d{4}|\d{2}))?"),
regex(r"(?P<n>\d+) (days?|ds?)(?P<ago>( ago)?)"),
regex(r"(?P<hr>\d{2}):(?P<mins>\d{2})"),
regex(r"^(\d+): \d+ windows \(.*\) \[\d+x\d+\]( \(attached\))?"),
regex(r"^(\d+):(\d+): (.*) \((\d+) panes\) \[(\d+)x(\d+)\]"),
regex(r"(?:\\\{start\\\}|\\\{end\\\})"),
regex(r"(.*)\s+-\s+(.*)"),
regex(r"(.*)\s+(\w+)$"),
regex(r"(.*)\s+(\w+)$"),
regex(r"(.*)\s+-\s+(.*)"),
regex(r"[[:lower:]]"),
regex(r"^\d+ (day|week|month|year)s?$"),
regex(r"^\d+ (day|week|month|year)s?$"),
regex(r"^[-+]?(0|[1-9][0-9_]*)$"),
regex(r"^([-+]?)0o?([0-7_]+)$"),
regex(r"^([-+]?)0x([0-9a-fA-F_]+)$"),
regex(r"^([-+]?)0b([0-1_]+)$"),
regex(r"^([-+]?)(\.[0-9]+|[0-9]+(\.[0-9]*)?([eE][-+]?[0-9]+)?)$"),
regex(r"^[+]?(\.inf|\.Inf|\.INF)$"),
regex(r"^-(\.inf|\.Inf|\.INF)$"),
regex(r"^(\.nan|\.NaN|\.NAN)$"),
regex(r"^(null|Null|NULL|~)$"),
regex(r"^(true|True|TRUE|yes|Yes|YES)$"),
regex(r"^(false|False|FALSE|no|No|NO)$"),
regex(r"(?m)^(\S+)/(\S+) (\S+)(?: \((.*)\))?$"),
regex("^(\\s+|;.*?(\n|$))+"),
regex("^\".*?\""),
regex(r"^[^\s\{\}()\[\]]+"),
regex(r"^-?\d+"),
regex("^([0-9]+)([KMG])?$"),
regex(r"^\w+"),
regex(r"^\d+"),
regex(r"\A(0x)?([a-fA-F0-9]+)\z"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{2})\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})?\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})?\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})?\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})?\)"),
regex(r"'(?P<title>[^']+)'\s+\((?P<year>\d{4})?\)"),
regex("[0-9]{3}-[0-9]{3}-[0-9]{4}"),
regex(r"^\d+$"),
regex(r"^[a-z]+$"),
regex(r"^\d+$"),
regex(r"^\d+$"),
regex(r"\d{4}-\d{2}-\d{2}"),
regex(r"^[0-9\p{L} _\\.]{3,16}$"),
regex(r"^attachment; filename=(.+)$"),
regex(r"(\\)(?P<head>\$[0-9A-Za-z_{])"),
regex(r"\$([[:word:]]+)"),
regex(r"\$\{([[:word:]]+)\}"),
regex(r"'[a-z]+'"),
regex(r"^\d{4}-\d{2}-\d{2}$"),
regex(r"-\d{2}-"),
regex(r"(\x9B|\x1B\[)[0-?]*[ -/]*[@-~]"),
regex("^[a-zA-Z]([a-zA-Z0-9_-]*)$"),
regex(r"^[Yy](\n?)$"),
regex(r"^[Nn](\n?)$"),
regex("^(?P<KEY>([^=]*))=(.*)$"),
regex("(.*)=(\"(?P<QVALUE>([^\"]*))\"|(?P<VALUE>(.*)))$"),
regex(r"\s+"),
regex(r"\s*[\n\r]+\s*"),
regex(r"^([0-9a-fA-F\.:/]+)\s+dev\s+([a-z0-9\.]+)\s*(.*)$"),
regex(r"^([0-9a-fA-F\.:/]+|default)\s+via\s+([a-z0-9\.:]+)\s+dev\s+([a-z0-9\.]+)\s*(.*)$"),
regex(r"^(blackhole)\s+([0-9a-fA-F\.:/]+)$"),
regex(r"^(unreachable)\s+([0-9a-fA-F\.:/]+)\s+dev\s+([a-z0-9\.]+)\s+(.*)$"),
regex(r"\s*[\n\r]+\s*"),
regex(r"^\d+:\s+([a-zA-Z0-9\.-]+)(@\S+)*:\s+(.*)$"),
regex(r"\s*link/ether\s+([a-f0-9:]+)\s+.*"),
regex(r"\s*inet[6]*\s+([0-9a-f:\./]+)\s+.*"),
regex(r"^(.*):(\d+): [^ ]* ([^ ]*)$"),
regex(r"[^\w -]"),
regex(r"^(\d{4}-\d{2}-\d{2})-(\d{3})-(.+)$"),
regex(r"^[a-zA-Z]+$"),
regex(r"^\{([a-zA-Z_]+)\}$"),
regex("(?m:^(\\d{3}) (.+)\r$)"),
regex("\"(.+)\""),
regex("(\\w+) [Tt]ype: (\\w+)"),
regex("(?m:^(\\d{3})-.+\r$)"),
regex("Entering Passive Mode \\((\\d+),(\\d+),(\\d+),(\\d+),(\\d+),(\\d+)\\)"),
regex("(?m:^(.+)\r$)"),
regex("^([d-])(?:[rwx-]{3}){3} +\\d+ +\\w+ +\\w+ +(\\d+) +(.+) +(.+)$"),
regex(r"([\./\-_]{0,1}(19|20)\d{2})[\./\-_]{0,1}(([0-3]{0,1}[0-9][\./\-_])|(\w{3,5}[\./\-_]))([0-3]{0,1}[0-9][\./\-]{0,1})"),
regex(r"(?i)publishdate|pubdate|timestamp|article_date|articledate|date"),
regex(r"type\((.*)\)"),
regex(r"Vec<(.*)>"),
regex(r"Option<(.*)>"),
regex(r"HashMap<[a-z0-9A-Z]+, *(.*)>"),
regex("Vec *< *(.*) *>"),
regex(r"Option *< *(.*) *>"),
regex(r"HashMap *< *[a-z0-9A-Z]+ *, *(.*) *>"),
regex(r"/\*.*?\*/|//.*"),
regex("^\\s*#\\s*include\\s+<([:print:]+)>\\s*$"),
regex("^\\s*#\\s*include\\s+\"([:print:]+)\"\\s*$"),
regex(r"^\s*#\s*version\s+(\d+)"),
regex(r"^\s*$"),
regex(r"(?P<addr>via \S+)"),
regex(r"(?P<src>src \S+)"),
regex(r"(.*)\[\d+\]"),
regex(r"(\d+).(\d+)"),
regex(r"(?P<c>[\\\.\+\*\?\(\)\|\[\]\{\}\^\$])"),
regex(r"^\w+$"),
regex("'[^']+'"),
regex(r"(?m)//.*"),
regex(r"^1\d{10}$"),
regex(r"(?i)^[\w.%+-]+@(?:[A-Z0-9-]+\.)+[A-Z]{2,4}$"),
regex(r"(?x)(?P<user_agent>[a-zA-Z\d-_]+\/[0-9\.]+)"),
regex(r"(?P<user_agent>[a-zA-Z\d-_]+/[0-9\.]+)"),
regex(r"Cell [0-9]{2,} - Address:"),
regex(r"([0-9a-zA-Z]{1}[0-9a-zA-Z]{1}[:]{1}){5}[0-9a-zA-Z]{1}[0-9a-zA-Z]{1}"),
regex(r"Signal level=(\d+)/100"),
regex(r"(?s)\[b\](.*?)\[/b\]"),
regex(r"(?s)\[i\](.*?)\[/i\]"),
regex(r"(?s)\[u\](.*?)\[/u\]"),
regex(r"(?s)\[s\](.*?)\[/s\]"),
regex(r"(?s)\[size=(\d+)](.*?)\[/size\]"),
regex(r"(?s)\[color=(.+)](.*?)\[/color\]"),
regex(r"(?s)\[center\](.*?)\[/center\]"),
regex(r"(?s)\[left\](.*?)\[/left\]"),
regex(r"(?s)\[right\](.*?)\[/right\]"),
regex(r"(?s)\[table\](.*?)\[/table\]"),
regex(r"(?s)\[td\](.*?)\[/td\]"),
regex(r"(?s)\[tr\](.*?)\[/tr\]"),
regex(r"(?s)\[th\](.*?)\[/th\]"),
regex(r"(?s)\[url\](.*?)\[/url\]"),
regex(r"(?s)\[url=(.+)\](.*?)\[/url\]"),
regex(r"(?s)\[quote\](.*?)\[/quote\]"),
regex(r"(?s)\[quote=(.+)\](.*?)\[/quote\]"),
regex(r"(?s)\[img=(\d+)x(\d+)(\b.*)?\](.*?)\[/img\]"),
regex(r"(?s)\[img=(.+)(\b.*)?\](.*?)\[/img\]"),
regex(r"(?s)\[img(\b.*)?\](.*?)\[/img\]"),
regex(r"(?s)\[ol\](.*?)\[/ol\]"),
regex(r"(?s)\[ul\](.*?)\[/ul\]"),
regex(r"(?s)\[list\](.*?)\[/list\]"),
regex(r"(?s)\[youtube\](.*?)\[/youtube\]"),
regex(r"(?s)\[youtube=(\d+)x(\d+)\](.*?)\[/youtube\]"),
regex(r"(?s)\[li\](.*?)\[/li\]"),
regex(r"loop\d+"),
regex(r"ram\d+"),
regex(r"md\d+"),
regex(r"(\d{2}):(\d{2}):(\d{2})"),
regex(r"(\d{1,2}):(\d{1,2}):(\d{1,2})"),
regex(r"[2-9]"),
regex(r"[1-9]"),
regex(r"[0-9]"),
regex(r"\d{10}"),
regex(r"\d{1}"),
regex(r"^\w+"),
regex(r"^\w+"),
regex(r"^(\w+\.? ?){2,3}$"),
regex(r"^[A-Z][a-z]+\.?$"),
regex(r"^[A-Z][A-Za-z]*\.?$"),
regex(r"http://lorempixel.com/100/100/\w+"),
regex(r"http://lorempixel.com/100/100/cats"),
regex("(?i:ß)"),
regex("(?i:\\x{0587})"),
regex("^\\\\([!-/:-@\\[-`\\{-~aftnrv]|[0-7]{1,3}|x[0-9a-fA-F]{2}|x\\{[0-9a-fA-F]{1,6}\\})"),
regex(r":\w+"),
regex(r"^:(\w+)$"),
regex(r"^(__\w+__)/(.*)"),
regex(r"(.)([A-Z])"),
regex("\\{:[^\\s]+\\}"),
regex(r"^-?\d+(\.\d)?"),
regex(r"^[a-zA-Z_]+[\w-]*[!?_]?"),
regex(r"^\("),
regex(r"^\)"),
regex(r"^\s+"),
regex(r"^(\d{4})-(\d{2})-(\d{2})(?:T|\W)(\d{2}):(\d{2}):(\d{2})(([\+|-]\d{2}):(\d{2}))?$"),
regex("\x1b\\[[^m]+m"),
regex(r"__.*?__"),
regex(r"(?i)@(?:time|clipboard|cursor|date)"),
regex(r"^Microsoft Windows \[Version\s(\d+\.\d+\.\d+)\]$"),
regex(r"ProductName:\s([\w\s]+)\n"),
regex(r"ProductVersion:\s(\w+\.\w+\.\w+)"),
regex(r"BuildVersion:\s(\w+)"),
regex(r"(\w+) Linux release"),
regex(r"release\s([\w\.]+)"),
regex(r"Distributor ID:\s(\w+)"),
regex(r"Release:\s([\w\.]+)"),
regex(r"typename type\-parameter\-\d+\-\d+::.+"),
regex(r"[^a-zA-Z\s!\./'\042_\$0-9]"),
regex(r"(\x1b[^m]*m|\x1b\[\d+C)"),
regex(r"(\x1b\[)([0-9]+)(C)"),
regex("^+(.*)\r\n"),
regex(r"^ffd8ffe0"),
regex(r"^89504e47"),
regex(r"^47494638"),
regex("^(/([^/~]|~[01])*)*$"),
regex("^#(/([^/~%]|~[01]|%[0-9a-fA-F]{2})*)*$"),
regex(r"^5.5.5-(\d{1,2})\.(\d{1,2})\.(\d{1,3})-MariaDB"),
regex(r"^(\d{1,2})\.(\d{1,2})\.(\d{1,3})(.*)"),
regex(r"^[0-9]{4}[0-9A-Z]{2}[0-9]{3}$"),
regex(r"UniqueIndexViolation: (\w+)"),
regex("^(.+?)(ss|i)es$"),
regex("^(.+?)([^s])s$"),
regex("^(.+?)eed$"),
regex("^(.+?)(ed|ing)$"),
regex("(at|bl|iz)$"),
regex("([^aeiouylsz]{2})$"),
regex("^(.+?[^aeiou])y$"),
regex("^(.+?)(icate|ative|alize|iciti|ical|ful|ness)$"),
regex("^(.+?)(s|t)(ion)$"),
regex("^(.+?)e$"),
regex(r"(.*) you are (.*)"),
regex(r"(.*) you are (.*)"),
regex(r"(.*) you are (.*)"),
regex("^\\s*\\*"),
regex("^\\s*@(\\w+)\\s+(.*)"),
regex(r"^\s*#"),
regex(r"\{(?P<cmd>\w+)(?::?\s*(?P<arg>.*))?\}"),
regex(r"\{(eot|end_of_tab):?\s*"),
regex(r"([^\[]*)(?:\[([^\]]*)\])?"),
regex("^[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)*$"),
regex(r"\b\w\w+\b"),
regex(r"\b\w\w+\b"),
regex(r"^(\d+)\.(\d+)\.(\d+)(?:-([\dA-Za-z-]+(?:\.[\dA-Za-z-]+)*))?(?:\+([\dA-Za-z-]+(?:\.[\dA-Za-z-]+)*))?$"),
regex(r"([[:alpha:]][[[:alnum:]]_]*)"),
regex(r"^\s*(\*+(\s+))?"),
regex(r"^\s*(\*+)?"),
regex("[0-9]+"),
regex("([0-9]+)@(?:nodes|n)?:([^@]+)?"),
regex(r"(?i)in (\d+) (second|minute|hour|day|week)s?"),
regex("^([A-Za-z0-9 -_:]+)\n-+\n"),
regex(r"^-?[0-9]+(\.[0-9]+)?([eE]-?[0-9]+)?$"),
regex(r"^-?[0-9]+$"),
regex(r"[^\w\s\pP]+"),
regex(r"[\r\n\v\f]"),
regex(r"\n{3,}"),
regex(r"(?x)[ \t\p{Zs} \\ / \| \x2044 ]+"),
regex(r"\p{Pd}+"),
regex(r"\p{Ps}+"),
regex(r"\p{Pe}+"),
regex(r"\p{Pc}+"),
regex(r"[©Ⓒⓒ]"),
regex(r"[^\w\s]+"),
regex(r"\s+"),
regex(r"[^0-9a-zA-Z_]"),
regex(r"[0-9]"),
regex(r"(?m)^Minion (\S*) did not respond\. No job will be sent\.$"),
regex(r"</?[^>]+?>"),
regex(r"\([^)]*\)"),
regex("@import \"([^\"]*)\";"),
regex(r"[A-Za-z\d-]{1,63}$"),
regex(r"([^A-Za-z0-9_\-.,:/@\n])"),
regex(r"\n"),
regex("(?P<num>[0-9]+)(?P<units>[dhms])"),
regex(r"(?:Chrome|CrMo|CriOS)/([.0-9]+)"),
regex(r"Vivaldi/([.0-9]+)"),
regex(r"Firefox/([.0-9]+)"),
regex(r"^Mozilla/[.0-9]+ \((?:Mobile|Tablet);(?:.*;)? rv:([.0-9]+)\) Gecko/[.0-9]+ Firefox/[.0-9]+$"),
regex(r"FxiOS/([.0-9]+)"),
regex(r"\(([^;)]+);FOMA;"),
regex(r"jig browser[^;]+; ([^);]+)"),
regex(r"(?i)rss(?:reader|bar|[-_ /;()]|[ +]*/)"),
regex(r"(?i)(?:bot|crawler|spider)(?:[-_ ./;@()]|$)"),
regex(r"(?i)(?:feed|web) ?parser"),
regex(r"(?i)watch ?dog"),
regex(r"Edge/([.0-9]+)"),
regex(r"MSIE ([.0-9]+);"),
regex(r"Version/([.0-9]+)"),
regex(r"Opera[/ ]([.0-9]+)"),
regex(r"OPR/([.0-9]+)"),
regex(r"Version/([.0-9]+)"),
regex(r"(?:SoftBank|Vodafone|J-PHONE)/[.0-9]+/([^ /;()]+)"),
regex(r"Trident/([.0-9]+);"),
regex(r" rv:([.0-9]+)"),
regex(r"IEMobile/([.0-9]+);"),
regex(r"(?:WILLCOM|DDIPOCKET);[^/]+/([^ /;()]+)"),
regex(r"Windows ([ .a-zA-Z0-9]+)[;\\)]"),
regex(r"^Phone(?: OS)? ([.0-9]+)"),
regex(r"iP(hone;|ad;|od) .*like Mac OS X"),
regex(r"Version/([.0-9]+)"),
regex(r"rv:(\d+\.\d+\.\d+)"),
regex(r"FreeBSD ([^;\)]+);"),
regex(r"CrOS ([^\)]+)\)"),
regex(r"Android[- ](\d+\.\d+(?:\.\d+)?)"),
regex(r"PSP \(PlayStation Portable\); ([.0-9]+)\)"),
regex(r"PLAYSTATION 3;? ([.0-9]+)\)"),
regex(r"PlayStation Vita ([.0-9]+)\)"),
regex(r"PlayStation 4 ([.0-9]+)\)"),
regex(r"BB10(?:.+)Version/([.0-9]+) "),
regex(r"BlackBerry(?:\d+)/([.0-9]+) "),
regex(r"; CPU(?: iPhone)? OS (\d+_\d+(?:_\d+)?) like Mac OS X"),
regex(r"Mac OS X (10[._]\d+(?:[._]\d+)?)(?:\)|;)"),
regex(r"^(?:Apache-HttpClient/|Jakarta Commons-HttpClient/|Java/)"),
regex(r"[- ]HttpClient(/|$)"),
regex(r"^(?:PHP|WordPress|CakePHP|PukiWiki|PECL::HTTP)(?:/| |$)"),
regex(r"(?:PEAR HTTP_Request|HTTP_Request)(?: class|2)"),
regex(r"(?:Rome Client |UnwindFetchor/|ia_archiver |Summify |PostRank/)"),
regex(r"Sleipnir/([.0-9]+)"),
regex(r"@@[a-z|A-Z|\d]+@@"),
regex(r"\w+"),
regex("^([^=]+)=(.*)$"),
regex(r":([a-zA-Z0-9_+-]+):"),
regex(r"git-codecommit\.([a-z0-9-]+)\.amazonaws\.com"),
regex(r"^submodule\.(?P<name>.*)\.(?P<key>[^=]*)=(?P<value>.*)$"),
regex(r"[ \n]:(.*?):"),
regex(r"private_token=\w{20}"),
regex("^(http://|https://)"),
regex(r"(?P<comp>et al\.)(?:\.)"),
regex(r"\.{3}"),
regex(r"(?P<number>[0-9]+)\.(?P<decimal>[0-9]+)"),
regex(r"\s\.(?P<nums>[0-9]+)"),
regex(r"(?:[A-Za-z]\.){2,}"),
regex(r"(?P<init>[A-Z])(?P<point>\.)"),
regex(r"(?P<title>[A-Z][a-z]{1,3})(\.)"),
regex(r"&==&(?P<p>[.!?])"),
regex(r"&\^&(?P<p>[.!?])"),
regex(r"&\*\*&(?P<p>[.!?])"),
regex(r"&=&(?P<p>[.!?])"),
regex(r"&##&(?P<p>[.!?])"),
regex(r"&\$&(?P<p>[.!?])"),
regex(r"@(?:_|\d+(?:/\d+(?:-\d+)?)?)"),
regex(r"<(\d+)>"),
regex(r"\((\d+),(\d+),(\d+),(\d+),(\d+),(\d+)\)"),
regex(r"\b(\d{4})(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})\b"),
regex(r"\s+(\d+)\s*$"),
regex(r"<countryCode>(.*?)</countryCode>"),
regex(r"<vatNumber>(.*?)</vatNumber>"),
regex(r"<name>(.*?)</name>"),
regex(r"<address>(?s)(.*?)(?-s)</address>"),
regex(r"<valid>(true|false)</valid>"),
regex(r"^ATU\d{8}$"),
regex(r"^BE0?\d{9, 10}$"),
regex(r"^BG\d{9,10}$"),
regex(r"^HR\d{11}$"),
regex(r"^CY\d{8}[A-Z]$"),
regex(r"^CZ\d{8,10}$"),
regex(r"^DK\d{8}$"),
regex(r"^EE\d{9}$"),
regex(r"^FI\d{8}$"),
regex(r"^FR[A-HJ-NP-Z0-9][A-HJ-NP-Z0-9]\d{9}$"),
regex(r"^DE\d{9}$"),
regex(r"^EL\d{9}$"),
regex(r"^HU\d{8}$"),
regex(r"^IE\d[A-Z0-9\+\*]\d{5}[A-Z]{1,2}$"),
regex(r"^IT\d{11}$"),
regex(r"^LV\d{11}$"),
regex(r"^LT(\d{9}|\d{12})$"),
regex(r"^LU\d{8}$"),
regex(r"^MT\d{8}$"),
regex(r"^NL\d{9}B\d{2}$"),
regex(r"^PL\d{10}$"),
regex(r"^PT\d{9}$"),
regex(r"^RO\d{2,10}$"),
regex(r"^SK\d{10}$"),
regex(r"^SI\d{8}$"),
regex(r"^ES[A-Z0-9]\d{7}[A-Z0-9]$"),
regex(r"^SE\d{10}01$"),
regex(r"^(GB(GD|HA)\d{3}|GB\d{9}|GB\d{12})$"),
regex("^mio"),
regex("y"),
regex("@([a-z]+)"),
regex("([A-Z-]+):(.*)"),
regex("^[a-zA-Z_][a-zA-Z0-9_]*$"),
regex(r"\d+\.\d+\.\d+"),
regex(r"\d+\.\d+\.\d+"),
regex(r"^Vec<(.+)>$"),
regex(r"\\(\r\n|\n\r|\n|\r)"),
regex(r"\\(.)"),
regex(r"\r\n|\n\r|\n|\r"),
regex(r"([\]\\:])"),
regex("^Bearer realm=\"(.+?)\",service=\"(.+?)\",scope=\"(.+?)\"$"),
regex(r"([+-]?\s*\d+[dD]\d+|[+-]?\s*\d+)"),
regex("E"),
regex("^F"),
regex("^S"),
regex(r"Change-Id: (I[a-f0-9]{40})$"),
regex(r"(refs|ref|fix|fixes|close|closes)\s+([A-Z]{2,5}-[0-9]{1,5})$"),
regex(r"(\d+)(\.(\d+))?(\.(\d+))?(.*)"),
regex(r"[A-Za-z0-9]"),
regex(r"^(\S*) (\d*)\.(\d*)\.(\d*)(-(\S*))?"),
regex(r"(\d*)\.(\d*)\.(\d*)(-(\S*))?"),
regex(r"^# CaseFolding-(\d+)\.(\d+)\.(\d+).txt$"),
regex(r"^([0-9A-F]+); [CF]; ([0-9A-F ]+);"),
regex("\r?\n\r?\n"),
regex("\r?\n"),
regex(r"^600"),
regex(r"^5019"),
regex(r"^4"),
regex(r"^(5[1-5]|2[2-7])"),
regex(r"^3[47]"),
regex(r"^3[0689]"),
regex(r"^6([045]|22)"),
regex(r"^(62|88)"),
regex(r"^35"),
regex(r"^[0-9]+$"),
regex(r"\d{1,} passed.*filtered out"),
regex(r"error(:|\[).*"),
regex(r"<(.*?)>"),
regex(r"<(.*?)>"),
regex(r"<(.*?)>"),
regex(r"<(.*?)>"),
regex(r"(?m)^incremental: re-using (\d+) out of (\d+) modules$"),
regex(r"(?m)^\s*Finished .* target\(s\) in ([0-9.]+) secs$"),
regex("(?m)(warning|error): (.*)\n  --> ([^:]:\\d+:\\d+)$"),
regex(r"(?m)^test (.*) \.\.\. (\w+)"),
regex(r"(?m)(\d+) passed; (\d+) failed; (\d+) ignored; \d+ measured"),
regex(r"^[^-]+-[0-9a-f]+\.js$"),
regex(r"\s*//\n"),
regex(r"/\*"),
regex(r"\*/"),
regex("\\s+"),
regex(r"`(\S+) v([0-9.]+)"),
regex("^\\[.+\\]"),
regex("^\\[\\[.+\\]\\]"),
regex(r"^https://github.com/([-_0-9a-zA-Z]+)/([-_0-9a-zA-Z]+)(/|.git)?$"),
regex(r"^https://gitlab.com/([-_0-9a-zA-Z]+)/([-_0-9a-zA-Z]+)(/|.git)?$"),
regex(r"(?m)(?P<symbol>_ZN[0-9]+.*E)"),
regex(r"^\s*\}(?:\)*;?|\s*else\s*\{)$"),
regex("[\u{001b}\u{009b}][\\[()#;?]*(?:[0-9]{1,4}(?:;[0-9]{0,4})*)?[0-9A-PRZcf-nqry=><]"),
regex(r"^\s*\*( |$)"),
regex(r"^(\s+)"),
regex(r"/\*|\*/"),
regex(r"^\s*//!"),
regex(r"^#![^\[].*?(\r\n|\n)"),
regex(r"cargo-install-update\.exe-v.+"),
regex(r"^<(?:(int|uint|str|float|path):)?([\w_][a-zA-Z0-9_]*)>$"),
regex(r"^@\S+/\S+"),
regex(r"^@\S+"),
regex(r"^\S+@\S+"),
regex(r"^b0000 {21} complete   20[-0-9T:+]+\s +\d+s\n$"),
regex(r"(?P<greeting>\S+?) (?P<name>\S+?)$"),
regex(r"([ \t]*)```haskell([\s\S]*?)```"),
regex(r"\b((?:a|b|t)\d*)\b"),
regex("NB"),
regex(r"(?i)\[[a-z0-9_-]+\]"),
regex(r"^(?i)(\[[a-z0-9_-]+\])+"),
regex(r"(?m:^ {0,3}\[[^\]]+\]:.+$)"),
regex(r"[^\p{L}\p{M}\p{N}\p{Pc} -]"),
regex(""),
regex("(?i)hi"),
regex("http[s]?://domain.org"),
regex("(?i)http[s]?://domain.org"),
regex("http://domain.org"),
regex("http://domain.org"),
regex("ad.html"),
regex("ad.html"),
regex("http://domain.org"),
regex("http://domain.org/nocookies.sjs"),
regex("http://domain.org/nocookies.sjs"),
regex("http://domain.org/hideme.jpg"),
regex("http://domain.org/ok.html"),
regex("http://domain.org/ok.html\\?except_this=1"),
regex("[A-Za-z0-9=]"),
regex(r"^nsq://"),
regex(r"[\s\t\r\n]"),
regex(r"([\{\[,])|([\}\]])"),
regex(r"[^.\d]+$"),
regex(r"\b"),
regex(r"--------- beginning of.*"),
regex(r"a|e|i|o|u"),
regex(r"^(\d+)([kMG])$"),
regex("\\.([A-Za-z0-9]{2,4})$"),
regex("([0-9]{3,4}p|[0-9]{3,4}x[0-9]{3,4})"),
regex("(?:^\\[([^]]+)\\]|- ?([^-]+)$)"),
regex("(?:[eE]([0-9]{2,3})|[^0-9A-Za-z]([0-9]{2,3})(?:v[0-9])?[^0-9A-Za-z])"),
regex("[sS]([0-9]{1,2})"),
regex("((?i)(?:PPV.)?[HP]DTV|(?:HD)?CAM|BRRIP|[^a-z]TS[^a-z]|(?:PPV )?WEB.?DL(?: DVDRip)?|HDRip|DVDRip|CamRip|W[EB]BRip|BluRay|BD|DVD|DvDScr|hdtv)"),
regex("((19[0-9]|20[01])[0-9])"),
regex("((?i)xvid|x264|h\\.?264)"),
regex("((?i)MP3|DD5\\.?1|Dual[- ]Audio|LiNE|DTS|AAC(?:\\.?2\\.0)?|AC3(?:\\.5\\.1)?)"),
regex("\\[([0-9A-F]{8})\\]"),
regex(r"(\d+)[xX](\d+)"),
regex(r".*(\d{4}-\d{2}-\d{2}).*"),
regex(r"<@(.+)>"),
regex("(\\.|\\*|\\?|\\[|\\]|\\^|\\$)"),
regex("(\\d{4})-(\\d{1,2})-(\\d{1,2}) ?(\\d{1,2})?:?(\\d{1,2})?:?(\\d{1,2})?"),
regex(r"^([A-Z]+)(?:\s(.+))?\s*"),
regex(r"(\w{1,2})\[(.+?)\]"),
regex(r"(?i)in (\d+) (second|minute|hour|day|week)s?"),
regex("^(?u:[0-9])+"),
regex("^(?u:[0-9])+(?u:\\.)(?u:[0-9])+"),
regex("^(?u:[A-Za-zª-ªµ-µº-ºÀ-ÖØ-öø-ˁˆ-ˑˠ-ˤˬ-ˬˮ-ˮͰ-ʹͶ-ͷͺ-ͽͿ-ͿΆ-ΆΈ-ΊΌ-ΌΎ-ΡΣ-ϵϷ-ҁҊ-ԯԱ-Ֆՙ-ՙա-ևא-תװ-ײؠ-يٮ-ٯٱ-ۓە-ەۥ-ۦۮ-ۯۺ-ۼۿ-ۿܐ-ܐܒ-ܯݍ-ޥޱ-ޱߊ-ߪߴ-ߵߺ-ߺࠀ-ࠕࠚ-ࠚࠤ-ࠤࠨ-ࠨࡀ-ࡘࢠ-ࢴऄ-हऽ-ऽॐ-ॐक़-ॡॱ-ঀঅ-ঌএ-ঐও-নপ-রল-লশ-হঽ-ঽৎ-ৎড়-ঢ়য়-ৡৰ-ৱਅ-ਊਏ-ਐਓ-ਨਪ-ਰਲ-ਲ਼ਵ-ਸ਼ਸ-ਹਖ਼-ੜਫ਼-ਫ਼ੲ-ੴઅ-ઍએ-ઑઓ-નપ-રલ-ળવ-હઽ-ઽૐ-ૐૠ-ૡૹ-ૹଅ-ଌଏ-ଐଓ-ନପ-ରଲ-ଳଵ-ହଽ-ଽଡ଼-ଢ଼ୟ-ୡୱ-ୱஃ-ஃஅ-ஊஎ-ஐஒ-கங-சஜ-ஜஞ-டண-தந-பம-ஹௐ-ௐఅ-ఌఎ-ఐఒ-నప-హఽ-ఽౘ-ౚౠ-ౡಅ-ಌಎ-ಐಒ-ನಪ-ಳವ-ಹಽ-ಽೞ-ೞೠ-ೡೱ-ೲഅ-ഌഎ-ഐഒ-ഺഽ-ഽൎ-ൎൟ-ൡൺ-ൿඅ-ඖක-නඳ-රල-ලව-ෆก-ะา-ำเ-ๆກ-ຂຄ-ຄງ-ຈຊ-ຊຍ-ຍດ-ທນ-ຟມ-ຣລ-ລວ-ວສ-ຫອ-ະາ-ຳຽ-ຽເ-ໄໆ-ໆໜ-ໟༀ-ༀཀ-ཇཉ-ཬྈ-ྌက-ဪဿ-ဿၐ-ၕၚ-ၝၡ-ၡၥ-ၦၮ-ၰၵ-ႁႎ-ႎႠ-ჅჇ-ჇჍ-Ⴭა-ჺჼ-ቈቊ-ቍቐ-ቖቘ-ቘቚ-ቝበ-ኈኊ-ኍነ-ኰኲ-ኵኸ-ኾዀ-ዀዂ-ዅወ-ዖዘ-ጐጒ-ጕጘ-ፚᎀ-ᎏᎠ-Ᏽᏸ-ᏽᐁ-ᙬᙯ-ᙿᚁ-ᚚᚠ-ᛪᛱ-ᛸᜀ-ᜌᜎ-ᜑᜠ-ᜱᝀ-ᝑᝠ-ᝬᝮ-ᝰក-ឳៗ-ៗៜ-ៜᠠ-ᡷᢀ-ᢨᢪ-ᢪᢰ-ᣵᤀ-ᤞᥐ-ᥭᥰ-ᥴᦀ-ᦫᦰ-ᧉᨀ-ᨖᨠ-ᩔᪧ-ᪧᬅ-ᬳᭅ-ᭋᮃ-ᮠᮮ-ᮯᮺ-ᯥᰀ-ᰣᱍ-ᱏᱚ-ᱽᳩ-ᳬᳮ-ᳱᳵ-ᳶᴀ-ᶿḀ-ἕἘ-Ἕἠ-ὅὈ-Ὅὐ-ὗὙ-ὙὛ-ὛὝ-ὝὟ-ώᾀ-ᾴᾶ-ᾼι-ιῂ-ῄῆ-ῌῐ-ΐῖ-Ίῠ-Ῥῲ-ῴῶ-ῼⁱ-ⁱⁿ-ⁿₐ-ₜℂ-ℂℇ-ℇℊ-ℓℕ-ℕℙ-ℝℤ-ℤΩ-Ωℨ-ℨK-ℭℯ-ℹℼ-ℿⅅ-ⅉⅎ-ⅎↃ-ↄⰀ-Ⱞⰰ-ⱞⱠ-ⳤⳫ-ⳮⳲ-ⳳⴀ-ⴥⴧ-ⴧⴭ-ⴭⴰ-ⵧⵯ-ⵯⶀ-ⶖⶠ-ⶦⶨ-ⶮⶰ-ⶶⶸ-ⶾⷀ-ⷆⷈ-ⷎⷐ-ⷖⷘ-ⷞⸯ-ⸯ々-〆〱-〵〻-〼ぁ-ゖゝ-ゟァ-ヺー-ヿㄅ-ㄭㄱ-ㆎㆠ-ㆺㇰ-ㇿ㐀-䶵一-鿕ꀀ-ꒌꓐ-ꓽꔀ-ꘌꘐ-ꘟꘪ-ꘫꙀ-ꙮꙿ-ꚝꚠ-ꛥꜗ-ꜟꜢ-ꞈꞋ-ꞭꞰ-ꞷꟷ-ꠁꠃ-ꠅꠇ-ꠊꠌ-ꠢꡀ-ꡳꢂ-ꢳꣲ-ꣷꣻ-ꣻꣽ-ꣽꤊ-ꤥꤰ-ꥆꥠ-ꥼꦄ-ꦲꧏ-ꧏꧠ-ꧤꧦ-ꧯꧺ-ꧾꨀ-ꨨꩀ-ꩂꩄ-ꩋꩠ-ꩶꩺ-ꩺꩾ-ꪯꪱ-ꪱꪵ-ꪶꪹ-ꪽꫀ-ꫀꫂ-ꫂꫛ-ꫝꫠ-ꫪꫲ-ꫴꬁ-ꬆꬉ-ꬎꬑ-ꬖꬠ-ꬦꬨ-ꬮꬰ-ꭚꭜ-ꭥꭰ-ꯢ가-힣ힰ-ퟆퟋ-ퟻ豈-舘並-龎ﬀ-ﬆﬓ-ﬗיִ-יִײַ-ﬨשׁ-זּטּ-לּמּ-מּנּ-סּףּ-פּצּ-ﮱﯓ-ﴽﵐ-ﶏﶒ-ﷇﷰ-ﷻﹰ-ﹴﹶ-ﻼＡ-Ｚａ-ｚｦ-ﾾￂ-ￇￊ-ￏￒ-ￗￚ-ￜ𐀀-𐀋𐀍-𐀦𐀨-𐀺𐀼-𐀽𐀿-𐁍𐁐-𐁝𐂀-𐃺𐊀-𐊜𐊠-𐋐𐌀-𐌟𐌰-𐍀𐍂-𐍉𐍐-𐍵𐎀-𐎝𐎠-𐏃𐏈-𐏏𐐀-𐒝𐔀-𐔧𐔰-𐕣𐘀-𐜶𐝀-𐝕𐝠-𐝧𐠀-𐠅𐠈-𐠈𐠊-𐠵𐠷-𐠸𐠼-𐠼𐠿-𐡕𐡠-𐡶𐢀-𐢞𐣠-𐣲𐣴-𐣵𐤀-𐤕𐤠-𐤹𐦀-𐦷𐦾-𐦿𐨀-𐨀𐨐-𐨓𐨕-𐨗𐨙-𐨳𐩠-𐩼𐪀-𐪜𐫀-𐫇𐫉-𐫤𐬀-𐬵𐭀-𐭕𐭠-𐭲𐮀-𐮑𐰀-𐱈𐲀-𐲲𐳀-𐳲𑀃-𑀷𑂃-𑂯𑃐-𑃨𑄃-𑄦𑅐-𑅲𑅶-𑅶𑆃-𑆲𑇁-𑇄𑇚-𑇚𑇜-𑇜𑈀-𑈑𑈓-𑈫𑊀-𑊆𑊈-𑊈𑊊-𑊍𑊏-𑊝𑊟-𑊨𑊰-𑋞𑌅-𑌌𑌏-𑌐𑌓-𑌨𑌪-𑌰𑌲-𑌳𑌵-𑌹𑌽-𑌽𑍐-𑍐𑍝-𑍡𑒀-𑒯𑓄-𑓅𑓇-𑓇𑖀-𑖮𑗘-𑗛𑘀-𑘯𑙄-𑙄𑚀-𑚪𑜀-𑜙𑢠-𑣟𑣿-𑣿𑫀-𑫸𒀀-𒎙𒒀-𒕃𓀀-𓐮𔐀-𔙆𖠀-𖨸𖩀-𖩞𖫐-𖫭𖬀-𖬯𖭀-𖭃𖭣-𖭷𖭽-𖮏𖼀-𖽄𖽐-𖽐𖾓-𖾟𛀀-𛀁𛰀-𛱪𛱰-𛱼𛲀-𛲈𛲐-𛲙𝐀-𝑔𝑖-𝒜𝒞-𝒟𝒢-𝒢𝒥-𝒦𝒩-𝒬𝒮-𝒹𝒻-𝒻𝒽-𝓃𝓅-𝔅𝔇-𝔊𝔍-𝔔𝔖-𝔜𝔞-𝔹𝔻-𝔾𝕀-𝕄𝕆-𝕆𝕊-𝕐𝕒-𝚥𝚨-𝛀𝛂-𝛚𝛜-𝛺𝛼-𝜔𝜖-𝜴𝜶-𝝎𝝐-𝝮𝝰-𝞈𝞊-𝞨𝞪-𝟂𝟄-𝟋𞠀-𞣄𞸀-𞸃𞸅-𞸟𞸡-𞸢𞸤-𞸤𞸧-𞸧𞸩-𞸲𞸴-𞸷𞸹-𞸹𞸻-𞸻𞹂-𞹂𞹇-𞹇𞹉-𞹉𞹋-𞹋𞹍-𞹏𞹑-𞹒𞹔-𞹔𞹗-𞹗𞹙-𞹙𞹛-𞹛𞹝-𞹝𞹟-𞹟𞹡-𞹢𞹤-𞹤𞹧-𞹪𞹬-𞹲𞹴-𞹷𞹹-𞹼𞹾-𞹾𞺀-𞺉𞺋-𞺛𞺡-𞺣𞺥-𞺩𞺫-𞺻𠀀-𪛖𪜀-𫜴𫝀-𫠝𫠠-𬺡丽-𪘀])+"),
regex("^(?u:d/d)((?u:[A-Za-zª-ªµ-µº-ºÀ-ÖØ-öø-ˁˆ-ˑˠ-ˤˬ-ˬˮ-ˮͰ-ʹͶ-ͷͺ-ͽͿ-ͿΆ-ΆΈ-ΊΌ-ΌΎ-ΡΣ-ϵϷ-ҁҊ-ԯԱ-Ֆՙ-ՙա-ևא-תװ-ײؠ-يٮ-ٯٱ-ۓە-ەۥ-ۦۮ-ۯۺ-ۼۿ-ۿܐ-ܐܒ-ܯݍ-ޥޱ-ޱߊ-ߪߴ-ߵߺ-ߺࠀ-ࠕࠚ-ࠚࠤ-ࠤࠨ-ࠨࡀ-ࡘࢠ-ࢴऄ-हऽ-ऽॐ-ॐक़-ॡॱ-ঀঅ-ঌএ-ঐও-নপ-রল-লশ-হঽ-ঽৎ-ৎড়-ঢ়য়-ৡৰ-ৱਅ-ਊਏ-ਐਓ-ਨਪ-ਰਲ-ਲ਼ਵ-ਸ਼ਸ-ਹਖ਼-ੜਫ਼-ਫ਼ੲ-ੴઅ-ઍએ-ઑઓ-નપ-રલ-ળવ-હઽ-ઽૐ-ૐૠ-ૡૹ-ૹଅ-ଌଏ-ଐଓ-ନପ-ରଲ-ଳଵ-ହଽ-ଽଡ଼-ଢ଼ୟ-ୡୱ-ୱஃ-ஃஅ-ஊஎ-ஐஒ-கங-சஜ-ஜஞ-டண-தந-பம-ஹௐ-ௐఅ-ఌఎ-ఐఒ-నప-హఽ-ఽౘ-ౚౠ-ౡಅ-ಌಎ-ಐಒ-ನಪ-ಳವ-ಹಽ-ಽೞ-ೞೠ-ೡೱ-ೲഅ-ഌഎ-ഐഒ-ഺഽ-ഽൎ-ൎൟ-ൡൺ-ൿඅ-ඖක-නඳ-රල-ලව-ෆก-ะา-ำเ-ๆກ-ຂຄ-ຄງ-ຈຊ-ຊຍ-ຍດ-ທນ-ຟມ-ຣລ-ລວ-ວສ-ຫອ-ະາ-ຳຽ-ຽເ-ໄໆ-ໆໜ-ໟༀ-ༀཀ-ཇཉ-ཬྈ-ྌက-ဪဿ-ဿၐ-ၕၚ-ၝၡ-ၡၥ-ၦၮ-ၰၵ-ႁႎ-ႎႠ-ჅჇ-ჇჍ-Ⴭა-ჺჼ-ቈቊ-ቍቐ-ቖቘ-ቘቚ-ቝበ-ኈኊ-ኍነ-ኰኲ-ኵኸ-ኾዀ-ዀዂ-ዅወ-ዖዘ-ጐጒ-ጕጘ-ፚᎀ-ᎏᎠ-Ᏽᏸ-ᏽᐁ-ᙬᙯ-ᙿᚁ-ᚚᚠ-ᛪᛱ-ᛸᜀ-ᜌᜎ-ᜑᜠ-ᜱᝀ-ᝑᝠ-ᝬᝮ-ᝰក-ឳៗ-ៗៜ-ៜᠠ-ᡷᢀ-ᢨᢪ-ᢪᢰ-ᣵᤀ-ᤞᥐ-ᥭᥰ-ᥴᦀ-ᦫᦰ-ᧉᨀ-ᨖᨠ-ᩔᪧ-ᪧᬅ-ᬳᭅ-ᭋᮃ-ᮠᮮ-ᮯᮺ-ᯥᰀ-ᰣᱍ-ᱏᱚ-ᱽᳩ-ᳬᳮ-ᳱᳵ-ᳶᴀ-ᶿḀ-ἕἘ-Ἕἠ-ὅὈ-Ὅὐ-ὗὙ-ὙὛ-ὛὝ-ὝὟ-ώᾀ-ᾴᾶ-ᾼι-ιῂ-ῄῆ-ῌῐ-ΐῖ-Ίῠ-Ῥῲ-ῴῶ-ῼⁱ-ⁱⁿ-ⁿₐ-ₜℂ-ℂℇ-ℇℊ-ℓℕ-ℕℙ-ℝℤ-ℤΩ-Ωℨ-ℨK-ℭℯ-ℹℼ-ℿⅅ-ⅉⅎ-ⅎↃ-ↄⰀ-Ⱞⰰ-ⱞⱠ-ⳤⳫ-ⳮⳲ-ⳳⴀ-ⴥⴧ-ⴧⴭ-ⴭⴰ-ⵧⵯ-ⵯⶀ-ⶖⶠ-ⶦⶨ-ⶮⶰ-ⶶⶸ-ⶾⷀ-ⷆⷈ-ⷎⷐ-ⷖⷘ-ⷞⸯ-ⸯ々-〆〱-〵〻-〼ぁ-ゖゝ-ゟァ-ヺー-ヿㄅ-ㄭㄱ-ㆎㆠ-ㆺㇰ-ㇿ㐀-䶵一-鿕ꀀ-ꒌꓐ-ꓽꔀ-ꘌꘐ-ꘟꘪ-ꘫꙀ-ꙮꙿ-ꚝꚠ-ꛥꜗ-ꜟꜢ-ꞈꞋ-ꞭꞰ-ꞷꟷ-ꠁꠃ-ꠅꠇ-ꠊꠌ-ꠢꡀ-ꡳꢂ-ꢳꣲ-ꣷꣻ-ꣻꣽ-ꣽꤊ-ꤥꤰ-ꥆꥠ-ꥼꦄ-ꦲꧏ-ꧏꧠ-ꧤꧦ-ꧯꧺ-ꧾꨀ-ꨨꩀ-ꩂꩄ-ꩋꩠ-ꩶꩺ-ꩺꩾ-ꪯꪱ-ꪱꪵ-ꪶꪹ-ꪽꫀ-ꫀꫂ-ꫂꫛ-ꫝꫠ-ꫪꫲ-ꫴꬁ-ꬆꬉ-ꬎꬑ-ꬖꬠ-ꬦꬨ-ꬮꬰ-ꭚꭜ-ꭥꭰ-ꯢ가-힣ힰ-ퟆퟋ-ퟻ豈-舘並-龎ﬀ-ﬆﬓ-ﬗיִ-יִײַ-ﬨשׁ-זּטּ-לּמּ-מּנּ-סּףּ-פּצּ-ﮱﯓ-ﴽﵐ-ﶏﶒ-ﷇﷰ-ﷻﹰ-ﹴﹶ-ﻼＡ-Ｚａ-ｚｦ-ﾾￂ-ￇￊ-ￏￒ-ￗￚ-ￜ𐀀-𐀋𐀍-𐀦𐀨-𐀺𐀼-𐀽𐀿-𐁍𐁐-𐁝𐂀-𐃺𐊀-𐊜𐊠-𐋐𐌀-𐌟𐌰-𐍀𐍂-𐍉𐍐-𐍵𐎀-𐎝𐎠-𐏃𐏈-𐏏𐐀-𐒝𐔀-𐔧𐔰-𐕣𐘀-𐜶𐝀-𐝕𐝠-𐝧𐠀-𐠅𐠈-𐠈𐠊-𐠵𐠷-𐠸𐠼-𐠼𐠿-𐡕𐡠-𐡶𐢀-𐢞𐣠-𐣲𐣴-𐣵𐤀-𐤕𐤠-𐤹𐦀-𐦷𐦾-𐦿𐨀-𐨀𐨐-𐨓𐨕-𐨗𐨙-𐨳𐩠-𐩼𐪀-𐪜𐫀-𐫇𐫉-𐫤𐬀-𐬵𐭀-𐭕𐭠-𐭲𐮀-𐮑𐰀-𐱈𐲀-𐲲𐳀-𐳲𑀃-𑀷𑂃-𑂯𑃐-𑃨𑄃-𑄦𑅐-𑅲𑅶-𑅶𑆃-𑆲𑇁-𑇄𑇚-𑇚𑇜-𑇜𑈀-𑈑𑈓-𑈫𑊀-𑊆𑊈-𑊈𑊊-𑊍𑊏-𑊝𑊟-𑊨𑊰-𑋞𑌅-𑌌𑌏-𑌐𑌓-𑌨𑌪-𑌰𑌲-𑌳𑌵-𑌹𑌽-𑌽𑍐-𑍐𑍝-𑍡𑒀-𑒯𑓄-𑓅𑓇-𑓇𑖀-𑖮𑗘-𑗛𑘀-𑘯𑙄-𑙄𑚀-𑚪𑜀-𑜙𑢠-𑣟𑣿-𑣿𑫀-𑫸𒀀-𒎙𒒀-𒕃𓀀-𓐮𔐀-𔙆𖠀-𖨸𖩀-𖩞𖫐-𖫭𖬀-𖬯𖭀-𖭃𖭣-𖭷𖭽-𖮏𖼀-𖽄𖽐-𖽐𖾓-𖾟𛀀-𛀁𛰀-𛱪𛱰-𛱼𛲀-𛲈𛲐-𛲙𝐀-𝑔𝑖-𝒜𝒞-𝒟𝒢-𝒢𝒥-𝒦𝒩-𝒬𝒮-𝒹𝒻-𝒻𝒽-𝓃𝓅-𝔅𝔇-𝔊𝔍-𝔔𝔖-𝔜𝔞-𝔹𝔻-𝔾𝕀-𝕄𝕆-𝕆𝕊-𝕐𝕒-𝚥𝚨-𝛀𝛂-𝛚𝛜-𝛺𝛼-𝜔𝜖-𝜴𝜶-𝝎𝝐-𝝮𝝰-𝞈𝞊-𝞨𝞪-𝟂𝟄-𝟋𞠀-𞣄𞸀-𞸃𞸅-𞸟𞸡-𞸢𞸤-𞸤𞸧-𞸧𞸩-𞸲𞸴-𞸷𞸹-𞸹𞸻-𞸻𞹂-𞹂𞹇-𞹇𞹉-𞹉𞹋-𞹋𞹍-𞹏𞹑-𞹒𞹔-𞹔𞹗-𞹗𞹙-𞹙𞹛-𞹛𞹝-𞹝𞹟-𞹟𞹡-𞹢𞹤-𞹤𞹧-𞹪𞹬-𞹲𞹴-𞹷𞹹-𞹼𞹾-𞹾𞺀-𞺉𞺋-𞺛𞺡-𞺣𞺥-𞺩𞺫-𞺻𠀀-𪛖𪜀-𫜴𫝀-𫠝𫠠-𬺡丽-𪘀])+)"),
regex("^(?u:\\()"),
regex("^(?u:\\))"),
regex("^(?u:\\*)"),
regex("^(?u:\\+)"),
regex("^(?u:,)"),
regex("^(?u:\\-)"),
regex("^(?u:/)"),
regex("^(?u:\\[)"),
regex("^(?u:\\])"),
regex("^(?u:\\^)"),
regex("^(?u:·)"),
regex("//+"),
regex("//+"),
regex(r"(\S*) .* (\S*) (REACHABLE|STALE|DELAY)"),
regex(r"-s (.*) --ip6-dst (.*)/.* bcnt = (.*)"),
regex(r"\buci(?:\s|$)"),
regex(r"\A[a-z0-9._=-]+\z"),
regex(r"/rusqbins/((?i)[A-F0-9]{8}\-[A-F0-9]{4}\-4[A-F0-9]{3}\-[89AB][A-F0-9]{3}\-[A-F0-9]{12})$"),
regex(r"/rusqbins/((?i)[A-F0-9]{8}\-[A-F0-9]{4}\-4[A-F0-9]{3}\-[89AB][A-F0-9]{3}\-[A-F0-9]{12})/requests/?$"),
regex(r"^(nightly|beta|stable)(?:-(\d{4}-\d{2}-\d{2}))?$"),
regex("^+(.*)\r\n"),
regex(r"^\* CAPABILITY (.*)\r\n"),
regex(r"^([a-zA-Z0-9]+) (OK|NO|BAD)(.*)"),
regex(r"^\* (\d+) EXISTS\r\n"),
regex(r"^\* (\d+) RECENT\r\n"),
regex(r"^\* FLAGS (.+)\r\n"),
regex(r"^\* OK \[UNSEEN (\d+)\](.*)\r\n"),
regex(r"^\* OK \[UIDVALIDITY (\d+)\](.*)\r\n"),
regex(r"^\* OK \[UIDNEXT (\d+)\](.*)\r\n"),
regex(r"^\* OK \[PERMANENTFLAGS (.+)\](.*)\r\n"),
regex(r"^[a-z]+ (\d+)$"),
regex(r"^[a-z]+ (\d+)$"),
regex(r"^[a-z]+ (\d+)$"),
regex(r"([^\\](\\\\)*)\\[\n\r][[:space:]]*"),
regex(r"(^\s*$)|(^\s*//\s*rustfmt-[^:]+:\s*\S+)"),
regex(r"^## `([^`]+)`"),
regex(r"([^\\](\\\\)*)\\[\n\r][[:space:]]*"),
regex(r"\s;"),
regex(r"^(0x)?([:digit:]+)$"),
regex(r"^([:digit:]+)[:space:]*<<[:space:]*([:digit:]+)$"),
regex(r"^[:space:]*([[:alnum:]_]+)([:space:]*=[:space:]*([:graph:]+))?[:space:]*,"),
regex(r"^#define[:space:]+([:graph:]+)[:space:]+([:graph:]+)"),
regex(r"^\s*pub mod (.+);$"),
regex(r"^\s*pub mod (.+);$"),
regex(r"(^\s*$)|(^\s*//\s*rustfmt-[^:]+:\s*\S+)"),
regex(r"^## `([^`]+)`"),
regex(r"\s;"),
regex(r"([^\\](\\\\)*)\\[\n\r][[:space:]]*"),
regex(r"(?s)(.*?)([ \t\r\n]*)(\{\{(\{?\S?\s*?[\w\.\s]*.*?\s*?\}?)\}\})([ \t\r\n]*)"),
regex(r"_ZN[\$\._[:alnum:]]*"),
regex(r"(?s)(.*?)([ \t\r\n]*)(\{\{(\{?\S?\s*?[\w\.\s]*.*?\s*?\}?)\}\})([ \t\r\n]*)"),
regex("(.+)=(.+)"),
regex("(.*):(.+)"),
regex("(.+):=(.+)"),
regex("(.*)==(.+)"),
regex(r"^\[([^\]]+)\]$"),
regex("([:blank:]*)$"),
regex("(\r?\n)[:blank:]*(\\{\\{~?[#!/](?:\\}?[^}])*\\}\\})[:blank:]*(:?\r?\n)?\\z"),
regex("(\r?\n[:blank:]*)(\\{\\{~?>(?:\\}?[^}])*\\}\\})[:blank:]*(:?\r?\n)?\\z"),
regex("((?:[:blank:]|\r?\n)*)(\r?\n)[:blank:]*$"),
regex("^([:blank:]*\r?\n)(.*)"),
regex(r"(?P<stamp>[\d-]*)_hello"),
regex(r"(\d+)s"),
regex(r"\n"),
regex(r"\r"),
regex(r"\t"),
regex(r"\\"),
regex(r"DELAY (-?\d+)ms"),
regex(r"Trim\((\d+), ?(\d+)\)"),
regex(r"spotify:[a-z]+:[a-zA-Z0-9]+"),
regex(r"[^\x00-\x7F]"),
regex(r"[']+"),
regex(r"\W+"),
regex(r"[ ]+"),
regex("PHPSESSID=([0-9a-f]+)"),
regex("[^0-9.,]"),
regex(r"(?:\b|(-)?)(\p{Sc})?((?:(?:\d{1,3}[\.,])+\d{3})|\d+)(?:[\.,](\d{2}))?\b"),
regex(r"<%=\s*(.+?)\s*%>"),
regex(r"(\s)"),
regex(r"#([A-Z3a-z]*):(.*)"),
regex("^-\\s?(-?[0-9]+)\\s*$"),
regex("^-\\s?(-?[0-9]+)\\s+(-?[0-9]+)"),
regex("^(.)\\s*(-?[0-9]+)\\s+(-?[0-9]+)\\s+(-?[0-9]+)\\s?(.*)"),
regex("^P\\s?(-?[0-9]+)"),
regex(r"^template\.add($|\..+$)"),
regex(r"^template\.sub($|\..+$)"),
regex(r"[^\w]"),
regex("\"([<>]?)([xcbB\\?hHiIlLqQfdspP]*)\""),
regex(r"^STEAM_([0-4]):([0-1]):([0-9]{1,10})$"),
regex(r"^\[([AGMPCgcLTIUai]):([0-4]):([0-9]{1,10})(:([0-9]+))?\]$"),
regex(r"^\w+"),
regex(r"^\s+"),
regex(r"^\w+"),
regex(r"^\s+"),
regex(r"^(\w+)\s+"),
regex(r"^([a-zA-Z0-9\.-]+)(?:\s+(\d+))$"),
regex(r"^([a-zA-Z0-9\.-]+)(?:\s+(\d+))$"),
regex(r"extern\s+crate\s+([a-z0-9_]+)\s*;(\s*//(.+))?"),
regex(r"(?m)^# "),
regex(r"(?m)^\s*fn +main *\( *\)"),
regex(r"(extern\s+crate\s+[a-z0-9_]+\s*;)"),
regex("(.*)_t([0-9]+)"),
regex(r"^.*(?:(?:youtu\.be/|v/|vi/|u/w/|embed/)|(?:(?:watch)?\?v(?:i)?=|\&v(?:i)?=))([^#\&\?]*).*"),
regex(r"^(?P<protocol>.*?)://(?P<public_key>.*?):(?P<secret_key>.*?)@(?P<host>.*?)/(?P<path>.*/)?(?P<project_id>.*)$"),
regex(r"Item #0: (.+)"),
regex(r"[a-zA-Z0-9]{8}"),
regex("/hello/(?P<name>[a-zA-Z]+)"),
regex("/hello/(?P<name>[a-zA-Z]+)"),
regex(r"\{(\w+)\}"),
regex("application/.*json"),
regex("application/json.*"),
regex("application/.*xml"),
regex("([\"'\\(\\[\\{{<\u{201c}])(\\s*)(.+?)(\\s*)([\"'\\)\\]\\}}>\u{201d}])"),
regex("([\\(\\[\\{{<\u{201c}]+)(\\s*)(.+?)(\\s*)([\\)\\]\\}}>\u{201d}]+)"),
regex(r"\{-[\s\S]*?-\}"),
regex(r"(?m);+\s*$"),
regex(r"(?m)^#(if|ifn?def|endif|else|include|elif).*"),
regex(r"'([^'\\]|\\[A-Z]{1,3}|\\.)'"),
regex(r"forall\s+(.*?)\."),
regex("/inf/(\\d+)"),
regex("/bq/(\\d+)"),
regex(r"#.*$"),
regex(r"^<(\S+)>"),
regex(r"^</(\S+)>"),
regex(r"#([:xdigit:]{2})([:xdigit:]{2})([:xdigit:]{2})"),
regex(r"rgb\((?: *(\d{1,3}),)(?: *(\d{1,3}),)(?: *(\d{1,3}))\)"),
regex(r"^([\w:]+)<(.+)>$"),
regex(r"^type-parameter-(\d+)-(\d+)$"),
regex(r"^([\w~]+)<[^<>]+>$"),
regex(r"(signals|Q_SIGNALS)\s*:"),
regex(r"(slots|Q_SLOTS)\s*:"),
regex(r"(public|protected|private)\s*:"),
regex(r"^([\w:]+)<(.+)>$"),
regex(r"^type-parameter-(\d+)-(\d+)$"),
regex(r"^([\w~]+)<[^<>]+>$"),
regex(r"(signals|Q_SIGNALS)\s*:"),
regex(r"(slots|Q_SLOTS)\s*:"),
regex(r"(public|protected|private)\s*:"),
regex("(\\d{2}\\.\\d{2}\\.\\d{2}) (\\d{2}:\\d{2}:\\d{2}) (.*)"),
regex(r"^api-[a-zA-Z0-9]{32}$"),
regex(r"^[-a-zA-Z0-9_=@,.;]+$"),
regex(r"\A\d+\.\d+\z"),
regex(r"^\.(.+?) +?(.+)$"),
regex(r"^\.([^\s]+)$"),
regex(r"^include! +([^\s]+)$"),
regex(r"^@(\d+)$"),
regex(r"^true|false$"),
regex(r"^(-?\d+)?\.[0-9]+$"),
regex(r"^(-?\d+)?$"),
regex(r"^#([0-9abcdefABCDEF]{6})$"),
regex(r"^'(.)'$"),
regex(r"^\$vi\((\d+)\)$"),
regex(r"^\$key\((\d+)\)$"),
regex("(?P<type>[A-Z^']+) (?P<route>[^']+) HTTP/(?P<http>[^']+)"),
regex(r"[A-F0-9]{8}"),
regex("[\\\\\"\x00-\x1f\x7f-\u{9f}\u{00ad}\u{0600}-\u{0604}\u{070f}\u{17b4}\u{17b5}\u{200c}-\u{200f}\u{2028}-\u{202f}\u{2060}-\u{206f}\u{feff}\u{fff0}-\u{ffff}]"),
regex("[\x00-\x1f\x7f-\u{9f}\u{00ad}\u{0600}-\u{0604}\u{070f}\u{17b4}\u{17b5}\u{200c}-\u{200f}\u{2028}-\u{202f}\u{2060}-\u{206f}\u{feff}\u{fff0}-\u{ffff}]"),
regex("'''|[\x00-\x09\x0b\x0c\x0e-\x1f\x7f-\u{9f}\u{00ad}\u{0600}-\u{0604}\u{070f}\u{17b4}\u{17b5}\u{200c}-\u{200f}\u{2028}-\u{202f}\u{2060}-\u{206f}\u{feff}\u{fff0}-\u{ffff}]"),
regex(r"/todos/(?P<id>\d+)"),
regex(r"[^a-zA-Z0 -]+"),
regex(r" {2,}"),
regex(r"(?m)//.*"),
regex("(?P<robot>C3PO)"),
regex(">|<|\"|&"),
regex(r"^\w+-\w+-[0123456789]{4}$"),
regex(r"^\w+@\w+@[0123456789]{4}$"),
regex(r"^\w+-\w+-[0123456789abcdef]{4}$"),
regex(r"^\w+-\w+-[0123456789忠犬ハチ公]{10}$"),
regex(r"^\w+-\w+$"),
regex(r"^\w+-\w+-[foo]{4}$"),
regex(r"^\w+-\w+-[0123456789忠犬ハチ公]{5}$"),
regex(r"(.*)"),
regex(r"rustc (.*)"),
regex(r"cargo (.*)"),
regex(r"xargo (.*)\n"),
regex(r"Open On-Chip Debugger (.*)"),
regex(r"arm-none-eabi-gcc \(GNU Tools for ARM Embedded Processors[^\)]*\) (.*)"),
regex(r"(?m).*\nBasic Open Source SAM-BA Application \(BOSSA\) Version (.*)\n"),
regex(r"(?m)SEGGER J-Link Commander (.*)\n"),
regex(r"(?m)Teensy Loader, Command Line, Version (.*)\n"),
regex(r"dfu-util (.*)\n"),
regex(r"^/static/[^\\/]+$"),
regex("\u{001B}\\[[\\d;]*[^\\d;]"),
regex("\u{001B}\\[[\\d;]*[^\\d;]"),
regex(r"[,.?!:;\s]+"),
regex(r"^\[\d+\]$"),
regex(r" (?P<key>[^\s]+):(?P<value>[^\s^/]+)"),
regex(r".*?\.(a|la|lo|o|ll|keter|bc|dyn_o|out|d|rlib|crate|min\.js|hi|dyn_hi|S|jsexe|webapp|js\.externs|ibc|toc|aux|fdb_latexmk|fls|egg-info|whl|js_a|js_hi|jld|ji|js_o|so.*|dump-.*|vmb|crx|orig|elmo|elmi|pyc|mod|p_hi|p_o|prof|tix)$"),
regex(r".*?\.(stats|conf|h|cache.*|dat|pc|info)$"),
regex(r".*?\.(exe|a|la|o|ll|keter|bc|dyn_o|out|d|rlib|crate|min\.js|hi|dyn_hi|jsexe|webapp|js\.externs|ibc|toc|aux|fdb_latexmk|fls|egg-info|whl|js_a|js_hi|jld|ji|js_o|so.*|dump-.*|vmb|crx|orig|elmo|elmi|pyc|mod|p_hi|p_o|prof|tix)$"),
regex(r".*?\.(stats|conf|h|cache.*)$"),
regex(r"(\.git|\.pijul|_darcs|\.hg)$"),
regex("test"),
regex(r"foo"),
regex(r"a+b"),
regex(r"a[ab]*b"),
regex(r"\s+"),
regex(r"\s+"),
regex(r"^\s*([^\s]+) %cellsplit<\d+>$"),
regex(r"^\s*([^\s]+) %cellsplit<\d+>$"),
regex(r"^[+\-]?[0-9]+"),
regex(r"^[+\-]?[0-9]+\.[0-9]*([eE][+\-]?[0-9]+)?"),
regex(r"^[*] OK"),
regex(r"FLAGS\s\((.+)\)"),
regex(r"\[PERMANENTFLAGS\s\((.+)\)\]"),
regex(r"\[UIDVALIDITY\s(\d+)\]"),
regex(r"(\d+)\sEXISTS"),
regex(r"(\d+)\sRECENT"),
regex(r"\[UNSEEN\s(\d+)\]"),
regex(r"\[UIDNEXT\s(\d+)\]"),
regex(r"\\(\{|\})"),
regex(r"(^|[^\\])\\\|"),
regex(r"\[([^\]]*)$"),
regex(r"\[(.*/.*)\]"),
regex(r"\{(-?\d+\\\.\\\.-?\d+)\}"),
regex(r"\{([^,]+)\}"),
regex(r"\{(([^\}].*)?(,|\|)(.*[^\\])?)\}"),
regex(r"^/"),
regex(r"(^|[^\\])(\{|\})"),
regex(r"^--- (?P<filename>[^\t\n]+)(?:\t(?P<timestamp>[^\n]+))?"),
regex(r"^\+\+\+ (?P<filename>[^\t\n]+)(?:\t(?P<timestamp>[^\n]+))?"),
regex(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@[ ]?(.*)"),
regex(r"^(?P<line_type>[- \n\+\\]?)(?P<value>.*)"),
regex("/?(?P<zoom>[0-9]?[0-9])/(?P<x>[0-9]{1,10})/(?P<y>[0-9]{1,10})(\\.[a-zA-Z]{3,4})?$"),
regex("^(?P<zoom>[0-9]?[0-9])/(?P<x>[0-9]{1,10})/(?P<y>[0-9]{1,10})$"),
regex("^(?P<scale>[0-9]+) (?P<zoom>[0-9]?[0-9])/(?P<x>[0-9]{1,10})/(?P<y>[0-9]{1,10})$"),
regex(r"^(?P<minlon>-?[0-9]{1,3}(\.[0-9]{1,10})?) (?P<minlat>-?[0-9]{1,3}(\.[0-9]{1,10})?) (?P<maxlon>-?[0-9]{1,3}(\.[0-9]{1,10})?) (?P<maxlat>-?[0-9]{1,3}(\.[0-9]{1,10})?)$"),
regex(r"^(?P<minlon>-?[0-9]{1,3}(\.[0-9]{1,10})?),(?P<minlat>-?[0-9]{1,3}(\.[0-9]{1,10})?),(?P<maxlon>-?[0-9]{1,3}(\.[0-9]{1,10})?),(?P<maxlat>-?[0-9]{1,3}(\.[0-9]{1,10})?)$"),
regex(r"^https?://(.+?):1400/xml"),
regex(r"^[a-z]{2}$"),
regex(r"[a-z]{2}"),
regex(r"[a-z]{2}"),
regex(r"[\s,]"),
regex(r"^aws_access_key_id = (.*)"),
regex(r"^aws_secret_access_key = (.*)"),
regex(r"^aws_access_key_id = (.*)"),
regex(r"^aws_secret_access_key = (.*)"),
regex(r"Span\([0-9 ,]*\)"),
regex(r"Span\([0-9 ,]*\)"),
regex(r"[\S]+"),
regex("[[:xdigit:]][70]"),
regex(r"^((?P<address>.*):)?(?P<port>\d+)$"),
regex(r"[\w\s=+-/]+\((\{(.|\n)*\})\);?"),
regex("^((?:.*)-)?ss(0|[1-9][0-9]*)\\.pip$"),
regex("^((?:.*)-)?ss(0|[1-9][0-9]*)-cl(0|[1-9][0-9]*)\\.piplog$"),
regex("^((?:.*)-)?ss(0|[1-9][0-9]*)\\.pip$"),
regex("^((?:.*)-)?ss(0|[1-9][0-9]*)-cl(0|[1-9][0-9]*)\\.piplog$"),
regex("^.*pn(0|[1-9][0-9]*)(-ss(0|[1-9][0-9]*)(\\.pip|-cl(0|[1-9][0-9]*)\\.piplog))?$"),
regex("^(.*)-ss(?:0|[1-9][0-9]*)(?:\\.pip|-cl(?:0|[1-9][0-9]*)\\.piplog)$"),
regex(r"(?i)[āáǎàēéěèōóǒòīíǐìūúǔùüǘǚǜńň]"),
regex(r"([aeoiuvnm])([0-4])$"),
regex(r"(?P<value>\d+)(?P<units>[a-z])"),
regex(r"^[A-Za-z0-9]*$"),
regex(r"^[A-Z][A-Z0-9]{2,}$"),
regex(r"^http://www\.emusic\.com"),
regex(r"^[A-Z][A-Z0-9]{2,}"),
regex(r"(^[\x{0}|\x{feff}|\x{fffe}]*|[\x{0}|\x{feff}|\x{fffe}]*$)"),
regex(r"\$([a-zA-Z0-9_]+)"),
regex("[\\n]+"),
regex("(?m)^\\n"),
regex("(?m)^\\n"),
regex(r"^(?P<major>\d+)\.(?P<minor>\d+)(?:\.(?P<patch>\d+))?(?:(?P<pre0>[a-z]+)(?P<pre1>\d*))?$"),
regex(r"^(\d+)\.(\d+)$"),
regex(r"^[rv]2\.6"),
regex("body value"),
regex("start marker"),
regex("end marker"),
regex("body value"),
regex("^([A-Za-z/ ]+): (.*)"),
regex(r"#([^\s=]+)*"),
regex(r"#(\S+)*"),
regex(r"#prio=(\d+)"),
regex(r"\[(\S+)\]"),
regex(r"#limit=(\d+)"),
regex(r"#tagged=(\S+)"),
regex(r"#rev\b"),
regex(r"#done\b"),
regex(r"#open\b"),
regex(r"#since=(\S+)"),
regex(r"#until=(\S+)"),
regex(r"#plot=(\S+)"),
regex(r"#n=(\d+)"),
regex(r"(\S+)"),
regex(r"(?P<y>\d+)y"),
regex(r"(?P<m>\d+)m"),
regex(r"(?P<w>\d+)w"),
regex(r"(?P<d>\d+)d"),
regex(r"(?P<h>\d+)h"),
regex(r"C-(.)"),
regex(r"^\.\./qt[^/]+/"),
regex("(href|src)=\"([^\"]*)\""),
regex("data_batch_[1-5].bin"),
regex("test_batch.bin"),
regex(r"^\d+.\d+s$"),
regex(r"^\d+:\d+$"),
regex(r"^\d+:\d+m$"),
regex(r"!!"),
regex(r"^([^`]*)`([^`]+)`(.*)$"),
regex(r"\*+"),
regex(r"([^\$]*)\$\{?([A-Za-z0-9\?\$_]+)\}?(.*)"),
regex(r"^ *alias +([a-zA-Z0-9_\.-]+)=(.*)$"),
regex(r"hi"),
regex(r".*?\t"),
regex(r".*?[\t ]"),
regex(r"(\{[0-9.,q]*?})"),
regex(r"[ \t\n]+"),
regex(r"[ \t\n]+"),
regex(r"([^ |]+( +\| +[^ |]*)+)|( +)"),
regex(r" +\| +"),
regex(","),
regex(".*?,"),
regex(".*?,"),
regex(","),
regex(r"\x1B\[(?:([0-9]+;[0-9]+[Hf])|([0-9]+[ABCD])|(s|u|2J|K)|([0-9;]*m)|(=[0-9]+[hI]))"),
regex(r"[-_./]\z"),
regex("^[ \t\r\n\x0c]*[#!]"),
regex(r"^[ \t\x0c]*[#!][^\r\n]*$"),
regex(r"^([ \t\x0c]*[:=][ \t\x0c]*|[ \t\x0c]+)$"),
regex(r":.+\."),
regex(r"\."),
regex(r":"),
regex(r"v(\d+)\.(\d+)\.(\d+)"),
regex(r"^([^-]+)-(.*)\.dat\.gz$"),
regex("^(.*?)(<=|<|==|>=|>)(.*?)$"),
regex(r"^[A-Za-z$_][A-Za-z0-9$_]*$"),
regex(r"^[0-9]+[cC]$"),
regex(r"^0b[0-1]+[cC]$"),
regex(r"^0x[0-9a-fA-F]+[cC]$"),
regex(r"^[0-9]+$"),
regex(r"^0b[0-1]+$"),
regex(r"^0x[0-9a-fA-F]+$"),
regex(r"^[0-9]+[lL]$"),
regex(r"^0b[0-1]+[lL]$"),
regex(r"^0x[0-9a-fA-F]+[lL]$"),
regex(r"^(\d+)(,(\d+))?([acd]).*$"),
regex(r"<BinaryState>(\d)(\|-?\d+)*</BinaryState>"),
regex(r"(http[s]?://[^\s]+)"),
regex(r"^\d+.*$"),
regex(r"^[\pL\pN]+$"),
regex("^(?P<min>[0-9]{1,10})(:(?P<max>[0-9]{1,10}))?$"),
regex(r"^(ns=(?P<ns>[0-9]+);)?(?P<t>[isgb])=(?P<v>.+)$"),
regex(r"^(.+?)\s*:\s*(.+)$"),
regex(r"^.*(?:(?:youtu\.be/|v/|vi/|u/w/|embed/)|(?:(?:watch)?\?v(?:i)?=|\&v(?:i)?=))([^#\&\?]*).*"),
regex("."),
regex(r"."),
regex(r".+"),
regex(r"."),
regex(r"foo"),
regex(r"/target/"),
regex(r".DS_Store"),
regex(r"\{\{ *([a-z\._]+) *\}\}"),
regex(r"^([^][]+)"),
regex(r"(\[[^][]*\])"),
regex(r"^([^][]+)"),
regex(r"(\[[^][]*\])"),
regex(r"^(\d+)/(\d+)$"),
regex(r"\s+"),
regex(r"<[a-z/][^>]*>"),
regex(r"(\([^)]*\)|♪[^♪]*♪|[A-Z]{2,} ?:)"),
regex(r"\s+"),
regex(r"^(\d(-| )?){9}(x|X|\d|(\d(-| )?){3}\d)$"),
regex(r"[^0-9X]"),
regex(r"Intel\(r\) SPMD Program Compiler \(ispc\), (\d+\.\d+\.\d+)"),
]
}
