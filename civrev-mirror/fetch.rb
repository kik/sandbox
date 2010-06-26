#!/usr/bin/ruby
require 'open-uri'
require 'kconv'
require 'zlib'

$KCODE = 'e'

U = "http://www7.atpages.jp/~civrev/pukiwikiplus/index.php?"
#U = "http://as305.dyndns.org/~kik/tmp/pukiwikiplus/index.php?"

DST_DIR = Time.now.strftime("%Y%m%d.%H%M%S")

$stderr.puts "DST_DIR: #{DST_DIR}"

Dir.mkdir(DST_DIR)
def mkdir777(f)
  Dir.mkdir(f)
  File.chmod(0777, f)
end
mkdir777(DST_DIR + "/wiki")
mkdir777(DST_DIR + "/backup")
mkdir777(DST_DIR + "/attach")

class String
  def to_u8
    Kconv.kconv(self, Kconv::UTF8, Kconv::EUC)
  end
  def to_H
    self.unpack("H*")[0].upcase
  end
  def uncref
    self.gsub('&quot;', '"').gsub('&lt;', '<').gsub('&gt;', '>').gsub('&amp;', '&')
  end
end

def fetch(url)
  c = 0
  while c < 10
    c += 1
    begin
      return open(url, "Referer" => U) {|f| f.read }
    rescue
      if c >= 10
        raise "HTTP error #{$!}"
      end
    end
    sleep 1
  end
end

def parse_list(body)
  b = body[/^<ul>(.|\n)*^<\/ul>/]
  lis = []
  b.each {|line|
    if line =~ /<a href="([^\"]*)"/
      lis << $1.sub(/^.*\?/, '')
    end
  }
  lis
end

def mirror_page(name)
  ename = URI.unescape(name)
  dname = ename.to_u8
  fname = ename.to_H
  $stderr.puts "GET: #{dname}"

  body = fetch(U + "cmd=source&page=#{name}")
  body =~ /<pre id=\"source\">((.|\n)*)^<\/pre><\/div>/
  src = $1
  open(DST_DIR + "/wiki/#{fname}.txt", "w") {|f|
    f.write(src.uncref)
  }

  backups = []
  body = fetch(U + "cmd=backup&page=#{name}")
  i = 1
  body.scan(/<a href=\"([^\"]*action=source)\"/) {|u|
    $stderr.puts "BACKUP: #{i} #{dname}"
    i += 1
    u = u[0]
    u.gsub!(/&amp;/,"&")
    body = fetch(u)
    body =~ /<em>\d+ \((\d\d\d\d-\d\d-\d\d) \([^\)]*\) (\d\d:\d\d:\d\d)\)<\/em>/
    t = Time.parse($1 + " " + $2)
    body =~ /^<pre>((.|\n)*)^<\/pre>/
    backups << [t, $1]
  }
  if backups.size > 0
    Zlib::GzipWriter.open(DST_DIR + "/backup/#{fname}.gz") {|f|
      backups.size.times{|i|
        t, b = backups[i]
        e = i == backups.size-1 ? Time.now : backups[i+1][0]
        f.puts(">>>>>>>>>> #{t.to_i} #{e.to_i}")
        f.puts(b.uncref)
      }
    }
  end
end

def parse_attach_list(body)
  lis = []
  body.scan(/<a href=\"([^\"]*pcmd=open[^\"]*)\"/) {|u|
    u = u[0]
    u.gsub!(/&amp;/,"&")
    lis << u
  }
  lis
end

def mirror_attach(url)
  url =~ /&file=([^&]+)/
  file = URI.unescape($1).to_H
  dfile = URI.unescape($1).to_u8
  url =~ /&refer=([^&]+)/
  ref = URI.unescape($1).to_H
  dref = URI.unescape($1).to_u8
  url =~ /&age=([^&]+)/
  age = $1
  $stderr.puts "ATTACH: #{dref} #{dfile}"
  body = fetch(url)
  name = DST_DIR + "/attach/#{ref}_#{file}" + (age ? "." + age : "")
  open(name, "w") {|f|
    f.write(body)
  }
end

body = fetch(U + "cmd=list")

pages = parse_list(body)

pages.each {|page|
  mirror_page(page)
}

body = fetch(U + "cmd=attach&pcmd=list")

atts = parse_attach_list(body)

atts.each {|url|
  mirror_attach(url)
}

system("rm -f current")
system("ln -sf #{DST_DIR} current")
system("tar -zcf archive/#{DST_DIR}.tar.gz #{DST_DIR}")
