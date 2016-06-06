################################################################################
# WeBWorK Online Homework Delivery System
# Copyright © 2000-2015 The WeBWorK Project, https://github.com/openwebwork
# 
# 
# This program is free software; you can redistribute it and/or modify it under
# the terms of either: (a) the GNU General Public License as published by the
# Free Software Foundation; either version 2, or (at your option) any later
# version, or (b) the "Artistic License" which comes with this package.
# 
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE.	 See either the GNU General Public License or the
# Artistic License for more details.
################################################################################


package WeBWorK::ContentGenerator::Instructor::Similar;
use base qw(WeBWorK::ContentGenerator::Instructor);

=head1 NAME

WeBWorK::ContentGenerator::Instructor::Similar - Look for similar problems
based on WeBWorK::ContentGenerator::Instructor::Compare

=cut

use strict;
use warnings;

#use CGI qw(-nosticky );
use WeBWorK::CGI;
use WeBWorK::Form;
use WeBWorK::Utils qw(readDirectory max);
use WeBWorK::Utils::Tasks qw(renderProblems);
use DBI;
use Data::Dumper;
use Digest::SHA;
use File::Basename;
use Text::ParseWords;

# don't realy need this
# only need this if we are going to be comparing files in this module
# which is a bad idea anyways
#use Algorithm::Diff::XS qw(LCSidx);

use File::Path qw(make_path);
use Cwd qw(realpath);

require WeBWorK::Utils::ListingDB;

#sub pre_header_initialize {
#	 my ($self) = @_;
#	 my $r = $self->r;
#}

my %SIMtables=(
	'path' 		=> 	'SIM_path',
	'pgfile' 	=> 	'SIM_pgfile',
	'filehash'	=>	'SIM_filehash',
	'filetokens'	=>	'SIM_filetokens',
	'filetokenshash'=>	'SIM_filetokenshash',
	'diffs'		=>	'SIM_diffs',
	
	'textfield'	=>	'SIM_textfield',
	'deltatextfield'=>	'SIM_deltatextfield',
);

my @SIM_tables_fields = (
[$SIMtables{path}, '
	path_id int(15) NOT NULL auto_increment,
	path varchar(255) NOT NULL,
	KEY (path),
	PRIMARY KEY (path_id)
'],
[$SIMtables{pgfile}, '
	pgfile_id int(15) NOT NULL auto_increment,
	path_id int(15) NOT NULL,
	filename varchar(255) NOT NULL,
	flag TINYINT(2) NOT NULL,
	KEY (flag),
	PRIMARY KEY (pgfile_id)
'],
[$SIMtables{filehash}, '
	pgfile_id int(15) NOT NULL,
	hash varchar(64) NOT NULL,
	KEY (hash),
	PRIMARY KEY (pgfile_id)
'],
[$SIMtables{filetokens}, '
	pgfile_id int(15) NOT NULL,
	tokens int(15) NOT NULL,
	KEY (tokens),
	PRIMARY KEY (pgfile_id)
'],
[$SIMtables{filetokenshash}, '
	pgfile_id int(15) NOT NULL,
	hash varchar(64) NOT NULL,
	KEY (hash),
	PRIMARY KEY (pgfile_id)
'],
[$SIMtables{diffs}, '
	pgfile_id int(15) NOT NULL,
	pgfile_id_sim int(15) NOT NULL,
	delta smallint(5) NOT NULL,
	subset smallint (5) NOT NULL,
	superset smallint (5) NOT NULL,
	KEY (pgfile_id_sim),
	KEY (delta),
	KEY (subset),
	KEY (superset),
	PRIMARY KEY (pgfile_id, pgfile_id_sim)
'],

[$SIMtables{textfield}, '
	field_id int(15) NOT NULL auto_increment,
	hash CHAR(64) NOT NULL,
	state TINYINT(2) NOT NULL,
	KEY (state),
	KEY (hash),
	PRIMARY KEY (file_id)
'],
[$SIMtables{deltatextfield}, '
	field_id int(15) NOT NULL,
	pgfile_id_sim int(15) NOT NULL,
	delta smallint(5) NOT NULL,
	KEY (delta),
	KEY (field_id),
	KEY (pgfile_id_sim),
	PRIMARY KEY (field_id, pgfile_id_sim)
'],

);

my %STATtables=(
	'raw' 		=> 	'STAT_raw',
	'course'	=>	'STAT_course',
	'user'		=>	'STAT_user',
	'set'		=>	'STAT_set',
	'problem'	=>	'STAT_problem',
	'pgfile'	=>	'STAT_pgfile',
	'path'		=>	'STAT_path',
	'answer'	=>	'STAT_answer',
	'statistics'=>	'STAT_statistics',
);

sub safe_get_id {
	my $dbh = shift;
	my $tablename = shift;
	my $idname = shift;
	my $whereclause = shift;
	my $wherevalues = shift;
	my $addifnew = shift;
	my @insertvalues = @_;
#print "\nCalled with $tablename, $idname, $whereclause, [".join(',', @$wherevalues)."], (".join(',', @insertvalues).")\n";

	my $query = "SELECT $idname FROM `$tablename` ".$whereclause;
	my $sth = $dbh->prepare($query);
	$sth->execute(@$wherevalues);
	my $idvalue;
	my @row;
	unless(@row = $sth->fetchrow_array()) {
		return 0 unless $addifnew;
		for my $j (0..$#insertvalues) {
			#print "Looking at ".$insertvalues[$j]."\n";
			if ($insertvalues[$j] ne "") {
				$insertvalues[$j] = '"'.$insertvalues[$j].'"';
			} else {
				$insertvalues[$j] = "NULL";
			}
		}
		#print "INSERT INTO $tablename VALUES( ".join(',',@insertvalues).")\n";
		# dbug "INSERT INTO $tablename VALUES( ".join(',',@insertvalues).")\n";
		$dbh->do("INSERT INTO `$tablename` VALUES(". join(',',@insertvalues) .")");
		$sth = $dbh->prepare($query);
		$sth->execute(@$wherevalues);
		@row = $sth->fetchrow_array();
	}
	$idvalue = $row[0];
	return($idvalue);
}

my $libraryRoot;
my $pendingRoot;

	sub comment_cleanup{
		my $string = shift;
		return "" unless defined $string;

		# we are going to break the string on 
		# the first non-quoted hash symbol		
		my @tokens = quotewords('#+', 1, $string);
		
		return $tokens[0] if (scalar @tokens);
		
		# now we have a string with unbalanced quotes...
		# try just splitting it over the hash symbol, and hope that 
		# the first part does not contain unbalanced quotes
		
		@tokens = split(/#+/,$string);
		
		# the easy way out: the string before the hash symbol
		# does not contain quotes
		return $tokens[0] unless ($tokens[0] =~ /\'|\"/);
		
		# harder way out: balanced quotes in the string
		# before the hash symbol
		my @words = quotewords('#+', 1, $tokens[0]);
		return $tokens[0] if (scalar @words);
		
		#give up: don't do anything to the string
		return $string;
	}
	
	sub cleanup{
		my $string=shift;
		chomp($string);
		#if the string is a comment string, ignore it
		if ($string =~/^\s*#/){
			$string="";
		}	
	
		#if the entire string is just whitespace, ignore it
		if ($string =~/^\s*$/){
			$string="";
		}	
	
		#replace repeated whitespace with single space
		$string =~ s/\s+/ /g;
			
		#remove whitespace in the start of the string
		$string =~ s/^\s//g;
	
		#remove whitespace in the end of the string
		$string =~ s/\s$//g;

		# the following is risky
		# truncate string with comments
 		if($string =~ /[^\\\$\&]#.*$/){
			$string = comment_cleanup($string);
 		}

		#remove whitespace in the end of the string
		$string =~ s/\s$//g;

		#add a single space at the end of the string, unless it is an empty string
		$string = $string." " unless ($string eq "");
	
		return $string;
	}

	# the version that keeps 'words' together and drops the whitespace
# 	sub make_split{
# 		my $string = shift;
# 	
# 		my @tokens = split(/\s/,$string);
# 		my @the_list = map {split(/(\W)/,$_)} @tokens;
# 		my @short_list = map { ($_ ne "") ? $_ : () } @the_list;
# 	}

	# the version that keeps 'words' together and keeps the spaces
	sub make_split{
		my $string = shift;	
		my @tokens = split(/(\W)/,$string);
		my @short_list = map { ($_ ne "") ? $_ : () } @tokens;
	}

	# the version that keeps space in place of whitespace, 
	# and separates everything into individual characters
# 	sub make_split{
# 		my $string = shift;
# 	
# 		my @tokens = split(//,$string);
# 		my @short_list = map { ($_ ne "") ? $_ : () } @tokens;
# 		return @short_list;
# 	}


sub gettokens{
	my $pg_file = shift;
	
        my $fh;
        open($fh, '<', $pg_file);
        my $line;
        my @file_lines;
        while ($line = <$fh>) {
		$line = cleanup($line);
		push (@file_lines, make_split($line)) unless ($line eq "");
        }
        close($fh);
        return \@file_lines;
}


sub gettokensfromdata{
	my $data = shift;
	
        my @file_tokens;
        my @file_lines;
        for my $line (@{$data}){
		$line = cleanup($line);
		push (@file_lines, $line) unless ($line eq "");
		push (@file_tokens, make_split($line)) unless ($line eq "");
        }
        return (\@file_tokens, \@file_lines) if wantarray;
        return \@file_tokens;
}


sub getsha256hash{
	my $filedata = shift;
	my $ctx = Digest::SHA->new("sha256");
	$ctx->add($filedata);
	my $hash = $ctx->hexdigest;
	$hash = "(none)" unless (defined $hash);	
	return $hash;
}

sub getsha256hashfile{
	my $filename = shift;
	return "(none)" unless ( -e $filename );
	my $ctx = Digest::SHA->new("sha256");
	$ctx->addfile($filename,'U');
	my $hash = $ctx->hexdigest;
	$hash = "(none)" unless (defined $hash);	
	return $hash;
}

sub gettokenstringfromarrayref{
	my $tokens = shift;
	return join("\t",@{$tokens});
}


sub getfilesbyhash{
	my $dbh = shift;
	my $hash = shift;
	
	$hash = '"'.$hash.'"';
	
	my $query = "SELECT f.filename, p.path 
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{filehash}` h 
		WHERE h.hash=$hash AND h.pgfile_id = f.pgfile_id AND p.path_id = f.path_id";
	my $rows = $dbh->selectall_arrayref($query);	
	my @filenames = ();
	for my $ref_row (@{$rows}){
		push(@filenames, $ref_row->[1].'/'.$ref_row->[0]);
	}
	return \@filenames; 
}

sub getfilesbytokenhash{
	my $dbh = shift;
	my $hash = shift;
	
	$hash = '"'.$hash.'"';
	
	my $query = "SELECT f.filename, p.path 
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{filetokenshash}` h 
		WHERE h.hash=$hash AND h.pgfile_id = f.pgfile_id AND p.path_id = f.path_id";
	my $rows = $dbh->selectall_arrayref($query);
	
	#print CGI::p(Dumper($rows));
	
	my @filenames = ();
	for my $ref_row (@{$rows}){
		push(@filenames, $ref_row->[1].'/'.$ref_row->[0]);
	}
	return \@filenames; 
}


sub table_exists{
    my ($dbh,$table_name) = @_;

    my $sth = $dbh->table_info(undef, 'webwork', $table_name, 'TABLE');

    $sth->execute;
    my @info = $sth->fetchrow_array;

    my $exists = scalar @info;
    return $exists;
}

sub sim_tables_exist{
	my $dbh = shift;
	
	return (table_exists($dbh, $SIMtables{pgfile}) && 
		table_exists($dbh, $SIMtables{path}) &&
		table_exists($dbh, $SIMtables{diffs}) &&
		table_exists($dbh, $SIMtables{filehash}) &&
		table_exists($dbh, $SIMtables{filetokens}) &&
		table_exists($dbh, $SIMtables{filetokenshash}) );
}

sub stat_tables_exist{
	my $dbh = shift;
	
	return (table_exists($dbh, $STATtables{pgfile}) && 
		table_exists($dbh, $STATtables{path}) &&
		table_exists($dbh, $STATtables{statistics}));
}

sub getsimilarfiles{
	my $dbh = shift;
	my $name = shift;
	
	return [] unless sim_tables_exist($dbh);
	
	$name =~ s|^Library/||;
	$name =~ s|^Pending/|:pending:/|;
	
	my $pgfile = basename($name);
	my $pgpath = dirname($name);
	
	my $fileid = undef;
	
	my $query = "SELECT f.pgfile_id 
		FROM `$SIMtables{pgfile}` f, `$SIMtables{path}` p
		WHERE p.path = ? AND f.path_id = p.path_id AND f.filename = ?";
	my $sth = $dbh->prepare($query);
	$sth->execute($pgpath, $pgfile);
	if (my @row = $sth->fetchrow_array()) {
		$fileid = $row[0];
	}
	
	if (!defined $fileid){
		print STDERR "Did not find the file |$name| in the database\n";
		return undef if(!defined $fileid);		
	}
	
	$query = "(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d
		WHERE d.pgfile_id_sim = $fileid AND f.pgfile_id = d.pgfile_id AND f.path_id = p.path_id
		ORDER BY d.delta DESC) 
		UNION 
		(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d
		WHERE d.pgfile_id = $fileid AND f.pgfile_id = d.pgfile_id_sim AND f.path_id = p.path_id
		ORDER BY d.delta DESC)
		ORDER by sort_column DESC";
	my $rows = $dbh->selectall_arrayref($query);
	
	# print CGI::p(Dumper($rows));
	
	my @delta_file = ();
	for my $ref_row( @{$rows}){
		push (@delta_file, [$ref_row->[0], $ref_row->[2].'/'.$ref_row->[1]]);
	}

	# print CGI::p(Dumper(\@delta_file));

	return \@delta_file;
}

sub getSimilarFilesOPL_dbh{
	my $dbh = shift;
	my $name = shift;
	
	my %results;

	$results{status} = 0;
	$results{data} = [];
	$results{count} = 0;
	
	if ( !sim_tables_exist($dbh) ){
		$results{status} = -1;
		return \%results;
	}
	
	$name =~ s|^Library/||;
	$name =~ s|^Pending/|:pending:/|;
	
	my $pgfile = basename($name);
	my $pgpath = dirname($name);
	
	my $fileid = undef;
	
	my $query = "SELECT f.pgfile_id 
		FROM `$SIMtables{pgfile}` f, `$SIMtables{path}` p
		WHERE p.path = ? AND f.path_id = p.path_id AND f.filename = ?";
	my $sth = $dbh->prepare($query);
	$sth->execute($pgpath, $pgfile);
	if (my @row = $sth->fetchrow_array()) {
		$fileid = $row[0];
	}
	
	if (!defined $fileid){
		#print STDERR "Did not find the file |$name| in the database\n";
		$results{status} = -2;
		return \%results;
	}
	
	$results{count} = 1;
	
	$query = "(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d
		WHERE d.pgfile_id_sim = $fileid AND f.pgfile_id = d.pgfile_id AND f.path_id = p.path_id
		AND p.path NOT LIKE \":pending:%\"
		ORDER BY d.delta DESC) 
		UNION 
		(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d
		WHERE d.pgfile_id = $fileid AND f.pgfile_id = d.pgfile_id_sim AND f.path_id = p.path_id
		AND p.path NOT LIKE \":pending:%\"
		ORDER BY d.delta DESC)
		ORDER by sort_column DESC";
	my $rows = $dbh->selectall_arrayref($query);
	
	# print CGI::p(Dumper($rows));
	
	for my $ref_row( @{$rows}){
		push (@{$results{data}}, [$ref_row->[0], $ref_row->[2].'/'.$ref_row->[1]]);
	}

	# print CGI::p(Dumper(\@delta_file));
	$results{count} = scalar @{$results{data}};

	return \%results;
}


sub route_get_all_similar_files{
	my $dbh = shift;
	my $name = shift;
	my $mode = shift;
	$mode = 0 unless (defined $mode);

	return getsimilarfiles($dbh, $name) if ($mode == 0);
	
	my $hr_results;
	if ($mode == 1){
		$hr_results = getSimilarFilesInDir_dbh($dbh, $name);
	}
	
	if ($mode == 2){
		$hr_results = getSimilarFilesInParentDir_dbh($dbh, $name);
	}
	
	if ($mode == 3){
		$hr_results = getSimilarFilesOPL_dbh($dbh, $name);
	}

	if ($hr_results->{status} == 0 ){
		return $hr_results->{data};
	}
	
	return {};
}

sub getsimilarfiles_ce{
	my $ce = shift;
	my $dbh = getDB($ce);
	my $name = shift;
	my $mode = shift;
	
	$mode = 0 unless (defined $mode); 

	return route_get_all_similar_files($dbh, $name, $mode);
}

sub getTopFiveSimilarFiles{
	my $ce = shift;
	my $dbh = getDB($ce);
	my $name = shift;
	
	my %results;

	$results{status} = 0;
	$results{data} = [];
	$results{count} = 0;
	
	if ( !sim_tables_exist($dbh) ){
		$results{status} = -1;
		return \%results;
	}
	
	$name =~ s|^Library/||;
	$name =~ s|^Pending/|:pending:/|;
	
	my $pgfile = basename($name);
	my $pgpath = dirname($name);
	
	my $fileid = undef;
	
	my $query = "SELECT f.pgfile_id 
		FROM `$SIMtables{pgfile}` f, `$SIMtables{path}` p
		WHERE p.path = ? AND f.path_id = p.path_id AND f.filename = ?";
	my $sth = $dbh->prepare($query);
	$sth->execute($pgpath, $pgfile);
	if (my @row = $sth->fetchrow_array()) {
		$fileid = $row[0];
	}
	
	if (!defined $fileid){
		#print STDERR "Did not find the file |$name| in the database\n";
		$results{status} = -2;
		return \%results;
	}
	
	my $query_count_1 = "SELECT COUNT(*) FROM `$SIMtables{diffs}` d WHERE d.pgfile_id = $fileid";
	my $rows_count_1 = $dbh->selectall_arrayref($query_count_1);
	my $query_count_2 = "SELECT COUNT(*) FROM `$SIMtables{diffs}` d WHERE d.pgfile_id_sim = $fileid";
	my $rows_count_2 = $dbh->selectall_arrayref($query_count_2);
	
	$results{count} = $rows_count_1->[0]->[0] +  $rows_count_2->[0]->[0];
	
	$query = "(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d
		WHERE d.pgfile_id_sim = $fileid AND f.pgfile_id = d.pgfile_id AND f.path_id = p.path_id
		ORDER BY d.delta DESC) 
		UNION 
		(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d
		WHERE d.pgfile_id = $fileid AND f.pgfile_id = d.pgfile_id_sim AND f.path_id = p.path_id
		ORDER BY d.delta DESC)
		ORDER by sort_column DESC
		LIMIT 5";
	my $rows = $dbh->selectall_arrayref($query);
	
	# print CGI::p(Dumper($rows));
	
	for my $ref_row( @{$rows}){
		push (@{$results{data}}, [$ref_row->[0], $ref_row->[2].'/'.$ref_row->[1]]);
	}

	# print CGI::p(Dumper(\@delta_file));

	return \%results;
}


sub getTopFiveSimilarFilesOPL{
	my $ce = shift;
	my $dbh = getDB($ce);
	my $name = shift;
	
	my %results;

	$results{status} = 0;
	$results{data} = [];
	$results{count} = 0;
	
	if ( !sim_tables_exist($dbh) ){
		$results{status} = -1;
		return \%results;
	}
	
	$name =~ s|^Library/||;
	$name =~ s|^Pending/|:pending:/|;
	
	#print "name: $name\n";
	
	my $pgfile = basename($name);
	my $pgpath = dirname($name);
	
	my $fileid = undef;
	
	my $query = "SELECT f.pgfile_id 
		FROM `$SIMtables{pgfile}` f, `$SIMtables{path}` p
		WHERE p.path = ? AND f.path_id = p.path_id AND f.filename = ?";
	my $sth = $dbh->prepare($query);
	$sth->execute($pgpath, $pgfile);
	if (my @row = $sth->fetchrow_array()) {
		$fileid = $row[0];
	}
	
	if (!defined $fileid){
		#print STDERR "Did not find the file |$name| in the database\n";
		$results{status} = -2;
		return \%results;
	}
	
	my $query_count_1 = "SELECT COUNT(*) FROM `$SIMtables{diffs}` d, `$SIMtables{path}` p, `$SIMtables{pgfile}` f 
		WHERE d.pgfile_id = $fileid
		AND d.pgfile_id_sim = f.pgfile_id
		AND f.path_id = p.path_id
		AND p.path NOT LIKE \":pending:%\"";
	my $rows_count_1 = $dbh->selectall_arrayref($query_count_1);
	my $query_count_2 = "SELECT COUNT(*) FROM `$SIMtables{diffs}` d, `$SIMtables{path}` p, `$SIMtables{pgfile}` f 
		WHERE d.pgfile_id_sim = $fileid
		AND d.pgfile_id = f.pgfile_id
		AND f.path_id = p.path_id
		AND p.path NOT LIKE \":pending:%\"";
	my $rows_count_2 = $dbh->selectall_arrayref($query_count_2);
	
	$results{count} = $rows_count_1->[0]->[0] +  $rows_count_2->[0]->[0];
	
	$query = "(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d
		WHERE d.pgfile_id_sim = $fileid 
		AND f.pgfile_id = d.pgfile_id AND f.path_id = p.path_id
		AND p.path NOT LIKE \":pending:%\"
		ORDER BY d.delta DESC) 
		UNION 
		(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d
		WHERE d.pgfile_id = $fileid 
		AND f.pgfile_id = d.pgfile_id_sim AND f.path_id = p.path_id
		AND p.path NOT LIKE \":pending:%\"
		ORDER BY d.delta DESC)
		ORDER by sort_column DESC
		LIMIT 5";
	my $rows = $dbh->selectall_arrayref($query);
	
	# print CGI::p(Dumper($rows));
	
	for my $ref_row( @{$rows}){
		push (@{$results{data}}, [$ref_row->[0], $ref_row->[2].'/'.$ref_row->[1]]);
	}

	# print CGI::p(Dumper(\@delta_file));

	return \%results;
}



sub getSimilarFilesInDir_dbh{
	my $dbh = shift;
	my $name = shift;
	
	my %results;

	$results{status} = 0;
	$results{data} = [];
	$results{count} = 0;
	
	if ( !sim_tables_exist($dbh) ){
		$results{status} = -1;
		return \%results;
	}
	
	$name =~ s|^Library/||;
	
	my $pgfile = basename($name);
	my $pgpath = dirname($name);
	
	my $fileid = undef;
	
	my $query = "SELECT f.pgfile_id 
		FROM `$SIMtables{pgfile}` f, `$SIMtables{path}` p
		WHERE p.path = ? AND f.path_id = p.path_id AND f.filename = ?";
	my $sth = $dbh->prepare($query);
	$sth->execute($pgpath, $pgfile);
	if (my @row = $sth->fetchrow_array()) {
		$fileid = $row[0];
	}
	
	if (!defined $fileid){
		#print STDERR "Did not find the file |$name| in the database\n";
		$results{status} = -2;
		return \%results;
	}
	
	#my $query_count_1 = "SELECT COUNT(*) FROM `$SIMtables{diffs}` d WHERE d.pgfile_id = $fileid";
	#my $rows_count_1 = $dbh->selectall_arrayref($query_count_1);
	#my $query_count_2 = "SELECT COUNT(*) FROM `$SIMtables{diffs}` d WHERE d.pgfile_id_sim = $fileid";
	#my $rows_count_2 = $dbh->selectall_arrayref($query_count_2);
	
	$results{count} = 1;
	
	# select similar files with the same path
	$query = "(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d, `$SIMtables{pgfile}` fsim 
		WHERE d.pgfile_id_sim = $fileid AND f.pgfile_id = d.pgfile_id AND f.path_id = p.path_id
		AND fsim.pgfile_id = d.pgfile_id_sim AND fsim.path_id = p.path_id
		ORDER BY d.delta DESC) 
		UNION 
		(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d, `$SIMtables{pgfile}` fsim 
		WHERE d.pgfile_id = $fileid AND f.pgfile_id = d.pgfile_id_sim AND f.path_id = p.path_id
		AND fsim.pgfile_id = d.pgfile_id AND fsim.path_id = p.path_id
		ORDER BY d.delta DESC)
		ORDER by sort_column DESC
		";
	my $rows = $dbh->selectall_arrayref($query);
	
	# print CGI::p(Dumper($rows));
	
	for my $ref_row( @{$rows}){
		push (@{$results{data}}, [$ref_row->[0], $ref_row->[2].'/'.$ref_row->[1]]);
	}

	# print CGI::p(Dumper(\@delta_file));
	$results{count} = scalar @{$results{data}};

	return \%results;	
}

sub getSimilarFilesInDir{
	my $ce = shift;
	my $dbh = getDB($ce);
	my $name = shift;
	
	return getSimilarFilesInDir_dbh($dbh, $name);
}

sub getParentPath{
	my $path = shift;
	my @dirs = File::Spec->splitdir($path);
	
	return "" if (scalar @dirs < 2);
	
	pop @dirs;
	my $parent = File::Spec->catdir(@dirs);
	return $parent;
}
sub getPathIdsWithSameParent{
	my $dbh = shift;
	my $path = shift;
	my $parent = getParentPath($path);
	
	$parent = $path if ($parent eq "");
	
	my $query = "SELECT p.path_id, p.path 
		FROM `$SIMtables{path}` p
		HAVING STRCMP('$parent', p.path)=-1";
	my $results = $dbh->selectall_arrayref($query);
	
	my @properids = ();
	for my $row (@$results){
		my $id = $row->[0];
		my $pathname = $row->[1];
		if ( ($pathname eq $parent) or (getParentPath($pathname) eq $parent) ){
			#warn "|$path| and |$pathname|";
			push(@properids, $id);
		}
	}
	
	return @properids;
}

sub getSimilarFilesInParentDir_dbh{
	my $dbh = shift;
	my $name = shift;
	
	my %results;

	$results{status} = 0;
	$results{data} = [];
	$results{count} = 0;
	
	if ( !sim_tables_exist($dbh) ){
		$results{status} = -1;
		return \%results;
	}
	
	$name =~ s|^Library/||;
	
	my $pgfile = basename($name);
	my $pgpath = dirname($name);
	
	my $fileid = undef;
	
	my $query = "SELECT f.pgfile_id 
		FROM `$SIMtables{pgfile}` f, `$SIMtables{path}` p
		WHERE p.path = ? AND f.path_id = p.path_id AND f.filename = ?";
	my $sth = $dbh->prepare($query);
	$sth->execute($pgpath, $pgfile);
	if (my @row = $sth->fetchrow_array()) {
		$fileid = $row[0];
	}
	
	if (!defined $fileid){
		#print STDERR "Did not find the file |$name| in the database\n";
		$results{status} = -2;
		return \%results;
	}
	
	#my $query_count_1 = "SELECT COUNT(*) FROM `$SIMtables{diffs}` d WHERE d.pgfile_id = $fileid";
	#my $rows_count_1 = $dbh->selectall_arrayref($query_count_1);
	#my $query_count_2 = "SELECT COUNT(*) FROM `$SIMtables{diffs}` d WHERE d.pgfile_id_sim = $fileid";
	#my $rows_count_2 = $dbh->selectall_arrayref($query_count_2);
	
	$results{count} = 1;
	
	# select similar files with the same path
	
	my @pathids = getPathIdsWithSameParent($dbh, $pgpath);
	
	if (scalar @pathids == 0){
		$results{status} = -2;
		return \%results;		
	}
	
	my $pathidsString = "(". join(', ',@pathids) .")";
	
	# warn "Pathids: |$pathidsString|";
	
	$query = "(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d, `$SIMtables{pgfile}` fsim 
		WHERE d.pgfile_id_sim = $fileid AND f.pgfile_id = d.pgfile_id AND f.path_id = p.path_id
		AND fsim.pgfile_id = d.pgfile_id AND fsim.path_id IN $pathidsString
		ORDER BY d.delta DESC) 
		UNION 
		(SELECT d.delta as sort_column, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{diffs}` d, `$SIMtables{pgfile}` fsim 
		WHERE d.pgfile_id = $fileid AND f.pgfile_id = d.pgfile_id_sim AND f.path_id = p.path_id
		AND fsim.pgfile_id = d.pgfile_id_sim AND fsim.path_id IN $pathidsString
		ORDER BY d.delta DESC)
		ORDER by sort_column DESC
		";
	my $rows = $dbh->selectall_arrayref($query);
	
	# print CGI::p(Dumper($rows));
	
	for my $ref_row( @{$rows}){
		push (@{$results{data}}, [$ref_row->[0], $ref_row->[2].'/'.$ref_row->[1]]);
	}

	# print CGI::p(Dumper(\@delta_file));
	
	$results{count} = scalar @{$results{data}};
	
	return \%results;
}

sub getSimilarFilesInParentDir{
	my $ce = shift;
	my $dbh = getDB($ce);
	my $name = shift;
	
	return getSimilarFilesInParentDir_dbh($dbh, $name);
	
}

sub getStatsOnPGFile{
	my $ce = shift;
	my $dbh = getDB($ce);
	my $name = shift;
	my $original_name = $name;
	
	my %results;

	$results{status} = 0;
	$results{data} = {};
	$results{count} = 0;
	
	if ( !stat_tables_exist($dbh) ){
		$results{status} = -1;
		return \%results;
	}
	
	$name =~ s|^Library/||;
	
	my $pgfile = basename($name);
	my $pgpath = dirname($name);
	
	# warn "|$pgfile|$pgpath|";
	
	my $fileid = undef;
	
	my $query = "SELECT f.pgfile_id 
		FROM `$STATtables{pgfile}` f, `$STATtables{path}` p
		WHERE p.path = ? AND f.path_id = p.path_id AND f.filename = ?";
	my $sth = $dbh->prepare($query);
	$sth->execute($pgpath, $pgfile);
	if (my @row = $sth->fetchrow_array()) {
		$fileid = $row[0];
	}
	
	if (!defined $fileid){
		# first attempt failed, will try a much deeper approach
		if (-e $original_name){
			my $realname = realpath($original_name);
			$realname =~ s|^$libraryRoot/||;
			$pgfile = basename($name);
			$pgpath = dirname($name);
			$sth->execute($pgpath, $pgfile);
			if (my @row = $sth->fetchrow_array()) {
				$fileid = $row[0];
			}
			if (!defined $fileid){
				$results{status} = -2;
				return \%results;
			}
		} else {
			$results{status} = -2;
			return \%results;
		}
	}
	
	$query = "SELECT 
		s.users_total, s.max_attempts, s.median_attempts, s.average_attempts, s.stdev_attempts,
		s.users_completed_total, s.max_attempts_completed, 
		s.median_attempts_completed, 
		s.average_attempts_completed, s.stdev_attempts_completed
		FROM `$STATtables{statistics}` s
		WHERE s.pgfile_id = $fileid";
	$sth = $dbh->prepare($query);
	$sth->execute();
	my $data_hr = $sth->fetchrow_hashref();
	$results{data} = $data_hr;
	
	if (scalar keys %{$data_hr} < 10){
		$results{status}=-2;
	}

	for my $hkey (keys %{$data_hr}){
		if (!defined $data_hr->{$hkey}){
			$results{status}=-2;
		}
	}
	
	return \%results;
}

sub getsimilarfiles_textfieldhash{
	my $dbh = shift;
	my $hash = shift;
			
	my $query = "SELECT d.delta, f.filename, p.path
		FROM `$SIMtables{path}` p, `$SIMtables{pgfile}` f, `$SIMtables{deltatextfield}` d, `$SIMtables{textfield}` t
		WHERE t.field_id = d.field_id AND t.hash = \"$hash\" AND f.pgfile_id = d.pgfile_id_sim AND f.path_id = p.path_id
		ORDER BY d.delta DESC";
	my $rows = $dbh->selectall_arrayref($query);
	my @delta_file = ();
	for my $ref_row( @{$rows}){
		push (@delta_file, [$ref_row->[0], $ref_row->[2].'/'.$ref_row->[1]]);
	}
	return \@delta_file;
}

sub get_file_ids_to_compare{
	my $db = shift;
	my $tokens = shift;

	# the cutoffs for the similarity search
	my $pvalue = 0.75;
	my $lowp = $pvalue/(2 - $pvalue);
	my $highp = (2 - $pvalue)/$pvalue;

	my $low = int($tokens*$lowp) - 1;
	$low = 0 if ($low < 0);
	my $high = int($tokens*$highp) + 1;
	
	my $query = "SELECT t.pgfile_id FROM `$SIMtables{filetokens}` t WHERE t.tokens>$low AND t.tokens<$high ORDER BY t.tokens";
	my $sth = $db->prepare($query);
	$sth->execute();		
	
	return $sth->fetchall_arrayref();
}

sub get_tokens_by_pgfile_id{
	my $db = shift;
	my $file_id = shift;
	my $query = "SELECT t.tokens FROM `$SIMtables{filetokens}` t WHERE t.pgfile_id=$file_id";
	my $sth = $db->prepare($query);
	$sth->execute();
	
	if (my @row = $sth->fetchrow_array()){
		return $row[0];
	} else {
		return undef;
	}
	return undef;
}

sub get_file_path_by_pgfile_id{
	my $db = shift;
	my $file_id = shift;
		
	my $query = "SELECT f.filename, p.path 
		FROM `$SIMtables{pgfile}` f, `$SIMtables{path}` p 
		WHERE p.path_id = f.path_id AND f.pgfile_id=$file_id";
	my $sth = $db->prepare($query);
	$sth->execute();
	
	if (my @row = $sth->fetchrow_array()){
		return $libraryRoot.'/'.$row[1].'/'.$row[0];
	}
	
	return undef;
}

sub get_data_by_pgfile_id{
	my $db = shift;
	my $file_id = shift;
	
	return gettokens(get_file_path_by_pgfile_id($db, $file_id));
}


sub getsimilarfilesfromdata{
	my $ce = shift;
	my $dbh = shift;
	my $data = shift;
	my $ref_qpos = shift;
	
	my ($tokens, $clean_lines) = gettokensfromdata($data);
	
	my $token_count = scalar @{$tokens};
	
	my $tokens_hash = getsha256hash(gettokenstringfromarrayref($tokens));

	my $ref_files_with_same_tokens = getfilesbytokenhash($dbh, $tokens_hash);
	
	# print CGI::p(Dumper($ref_files_with_same_tokens));
	
	my @db_data = ();
	
	if (defined $ref_files_with_same_tokens->[0]){
		push (@db_data, [10000, $ref_files_with_same_tokens->[0]]);
	};
	
	if (defined $db_data[0]){
		my $ref_files = getsimilarfiles($dbh, $db_data[0]->[1]);
		push (@db_data, @{$ref_files});
		return \@db_data;
	};
	
	# no easy way to compare the textfield to existing files
	# store the file, add it to the queue, and return nothing
	my $ref_files = getsimilarfiles_textfieldhash($dbh, $tokens_hash);
	if (scalar @{$ref_files}){
		return $ref_files;
	}
	
	my $newfile = storeTextField($ce, $tokens_hash, $clean_lines);
	# $$ref_qpos = addToQueue($dbh, $newfile);
	
	return undef;
	
}

sub getDB {
	my $ce = shift;
	my $dbh = DBI->connect(
		$ce->{problemLibrary_db}->{dbsource},
		$ce->{problemLibrary_db}->{user},
		$ce->{problemLibrary_db}->{passwd},
		{
			PrintError => 0,
			RaiseError => 1,
		},
	);
	die "Cannot connect to problem library database" unless $dbh;
	return($dbh);
}

sub storeTextField{
	my $ce = shift;
	my $hash = shift;
	my $data = shift;
	
	my $hash_path = substr($hash, 0, 2);
	
	my $filename_path = $ce->{courseDirs}->{templates}.'/textFieldFiles/'.$hash_path.'/';
	
	my $filename = $filename_path.$hash;
	
	make_path($filename_path);
	
	open(my $fh, ">", $filename);
	print $fh join("\n", @{$data}); 
	print $fh "\n";
	close($fh);
	
	return $filename;
}

sub addToQueue{
	my $dbh = shift;
	my $file = shift;
	
	my $id =safe_get_id(
		$dbh,
		$SIMtables{queue}, 'file_id',
		qq(WHERE filename = ?), [$file], 1, "", 
		$file, 0);
	
	return $id;
}

sub make_real_full_path{
	my $db_path = shift;
	if ($db_path =~ /^:pending:/){
		$db_path =~ s|^:pending:|$pendingRoot| if (defined $pendingRoot);
		return $db_path;
	}
	return $libraryRoot.'/'.$db_path;
}

sub make_real_local_path{
	my $db_path = shift;
	if ($db_path =~ /^:pending:/){
		$db_path =~ s|^:pending:|Pending|;
		return $db_path;
	}

	if ($db_path =~ /^Pending/){
		return $db_path;
 	}
	
	if ($db_path =~ /^Library/){
		return $db_path;
	}

	return 'Library/'.$db_path;
}


sub body {
	my ($self) = @_;

	my $r = $self->r;
	my $ce = $r->ce;	# course environment
	my $db = $r->db;	# database
	my $dbh = getDB($ce);	# Library DB
	my $j;			# garden variety counter

	my $userName = $r->param('user');
	
	$libraryRoot = $ce->{problemLibrary}->{root};
	$libraryRoot =~ s|/+$||;
	
	$pendingRoot = $ce->{pendingLibrary}->{root};
	$pendingRoot =~ s|/+$|| if (defined $pendingRoot);	
	
	my $user = $db->getUser($userName); # checked
	die "record for user $userName (real user) does not exist."
		unless defined $user;

	### Check that this is a professor
	my $authz = $r->authz;
	unless ($authz->hasPermissions($userName, "modify_problem_sets")) {
		print "User $userName returned " .
			$authz->hasPermissions($user, "modify_problem_sets") .
			" for permission";
		return(CGI::div({class=>'ResultsWithError'},
		  CGI::em("You are not authorized to access the Instructor tools.")));
	}

	my $path = $r->param('path') || '';
	# $path =~ s|^Library/||;
	
	# the mode of operation
	my $mode = $r->param('sim_depth') || '0';
	
	my $file_text = $r->param('filetext') || '';
	if ($r->param('clear')) {
		$path = '';
		$file_text = '';
		$mode = 0;
	}
	my @pathlist = ();
	push @pathlist, $path if $path;
	# push @pathlist, $path2 if $path2;
# 	my @rendered = renderProblems(r=> $r,
# 		user => $user,
# 		problem_list => \@pathlist,
# 		displayMode => 'images');

	##########	Extract information computed in pre_header_initialize
	print CGI::start_form({-method=>"POST", -action=>$r->uri, -name=>'mainform'}),
		$self->hidden_authen_fields;
	print CGI::p('File Path on this Server: ', CGI::br(),
		'[this course]/', CGI::textfield(-name=>"path",
		-default=>"$path",
		-override=>1, -size=>90));
# 	print CGI::p('Paste File Text Here', CGI::br(), CGI::textarea(-name=>"filetext",
# 		-default=>$file_text,
# 		-override=>1, -rows=>3, -columns=>70));
	print CGI::p(CGI::submit(-name=>"find",
		-value=>"Find Similar"));
	print CGI::p(CGI::submit(-name=>"clear",
		-value=>"Clear"));
	print CGI::end_form(), "\n";	
	
	
	if ($path ne ''){
		print CGI::a({name=>"topline", id=>"topline"},"");
		print CGI::h2("Results for file |$path|");
		my $filenamehash = getsha256hashfile($ce->{courseDirs}->{templates}.'/'.$path);
		print CGI::p('Hash for the file: '. $filenamehash);
		my $samefiles = getfilesbyhash($dbh, $filenamehash);
		print '<hr size="5" color="blue" />';	
		print CGI::p("Files with the same hash as |$path|:",
			CGI::br(),
			join(CGI::br(), @{$samefiles})
			);

		my $similar_files = route_get_all_similar_files($dbh, $path, $mode);
		$similar_files=[@{$similar_files}[0..19]] if (scalar @{$similar_files} > 20);

		my $cnt = 0;
		print '<hr size="5" color="blue" />';	
		for my $sim (@{$similar_files}){
			my $sim_str = (sprintf("%6.2f", $sim->[0]/100)) .'%: |'.make_real_local_path($path).'| vs. |'.make_real_local_path($sim->[1]).'|';
			print CGI::a({href=>"#sim".$cnt}, $sim_str);
			print CGI::br();
			$cnt++;
		}
		$cnt = 0;
		for my $sim (@{$similar_files}){
			print '<hr size="5" color="blue" />';	
			my $sim_str = (sprintf("%6.2f", $sim->[0]/100)) .'%: |'.make_real_local_path($path).'| vs. |'.make_real_local_path($sim->[1]).'|';
			print CGI::a({name=>"sim".$cnt, id=>"sim".$cnt},"");
			print CGI::h3($sim_str);
			print CGI::a({href=>"#topline"}, "Back to top");
			print CGI::br();
			my $rp1 = make_real_local_path($path);
			my $rp2 = make_real_local_path($sim->[1]);
			my $n1 = "$ce->{courseDirs}->{templates}/". make_real_local_path($path);
			my $n2 = "$ce->{courseDirs}->{templates}/". make_real_local_path($sim->[1]);
			my $dout = `hdiff -l 500 -t " " -c "$rp1" -C "$rp2" -N "$n1" "$n2"`;
			print $dout;
			print CGI::a({href=>"#topline"}, "Back to top");
			print CGI::br();
			$cnt++;
		}
		print '<hr size="5" color="blue" />';

	}
	
	if ($file_text ne ''){
		$file_text =~ s/\r\n/\n/msg; # strip away any windows-style EOLs
		$file_text =~ s/\r/\n/msg; # strip away any old-mac-style EOLs
		
		print CGI::h2("Results for contents of the text field");
		
		my @text_lines = split("\n",$file_text);
		
		my ($file_tokens, $clean_lines) = gettokensfromdata(\@text_lines);
		print CGI::p('Minimized file lines:', CGI::br(),
			join(CGI::br(), @{$clean_lines})
			);
		print '<hr size="5" color="blue" />';	
		print CGI::p('File tokens:', CGI::br(),
			' |'.join('| |', @{$file_tokens}).'| '
			);
		print '<hr size="5" color="blue" />';	
		
			
		my $textfieldhash = getsha256hash($file_text);
		
		print CGI::p('Hash for textfield: '. $textfieldhash);
		
		my $samefiles_text = getfilesbyhash($dbh, $textfieldhash);
		
		print '<hr size="5" color="blue" />';	
		print CGI::p("Files with the same hash as the textfield:",
			CGI::br(),
			join(CGI::br(), @{$samefiles_text})
			);
			
		my $queue_pos = undef;
		my $similar_files = getsimilarfilesfromdata($ce, $dbh, \@text_lines, \$queue_pos);
		my @similar_files_str;
		for my $sim (@{$similar_files}){
			push(@similar_files_str, (sprintf("%6.2f", $sim->[0]/100)) .'%: |'.$sim->[1].'|'); 
		}
		
		print '<hr size="5" color="blue" />';	
		print CGI::p("Files similar to the contents of textfield:",
			CGI::br(),
			join(CGI::br(), @similar_files_str)
			);

		if ( defined $queue_pos ){
			print CGI::p("File comparison was queued with id=|$queue_pos|");
		}
		print '<hr size="5" color="blue" />';	
	}
	

		

	return "";	
}


=head1 AUTHOR

Written by Alex Basyrov, basyrova (at) uwstout.edu,
based on 
WeBWorK::ContentGenerator::Instructor::Compare

=cut



1;
