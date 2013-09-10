#!/local/bin/perl

use Furl;
use strict;



    my $furl = Furl->new(
        agent   => 'MyGreatUA/2.0',
        timeout => 10,
    );


# This is a test of the Webwork RESTful webservice
#
# This document tests the User routes. 
#
# First, make sure that you have a user with instructor priviledges and a valid session key for a course


  
my $url_head = 'http://localhost/test/';

  # my $content = $lwpcurl->post($post_url, $hash_form, $referer);

my $user='profa';
my $key='xJuvxYyETp5y8K1YxHsZX5lMFAfJYFad';
my $course_id='maa101';

my $params = {user=>$user, course=>$course_id,session_key=>$key};
my ($res,$url);

## test #1  

# get a list of all problem sets 


if ("1" ~~ @ARGV){

	my $routeName = "courses/maa101/sets";

	print "Testing GET /$routeName  \n";

	$url = $url_head . "$routeName";


	$res = $furl->request(method=>'GET',url=>$url,content=>$params);

	die $res->status_line unless $res->is_success;
	print $res->content;

}

## test #2 

# get problem set xyz123


if ("2" ~~ @ARGV){

	my $routeName = "courses/maa101/sets/xyz123";

	print "Testing GET /$routeName  \n";

	$url = $url_head . "$routeName";


	$res = $furl->request(method=>'GET',url=>$url,content=>$params);

	die $res->status_line unless $res->is_success;
	print $res->content;

}

## test #3

# delete problem set xyz123


if ("3" ~~ @ARGV){

	my $routeName = "courses/maa101/sets/xyz123";

	print "Testing DELETE /$routeName  \n";

	$url = $url_head . "$routeName";


	$res = $furl->request(method=>'DELETE',url=>$url,content=>$params);

	die $res->status_line unless $res->is_success;
	print $res->content;

}

## test #4

# create problem set xyz123


if ("4" ~~ @ARGV){

	my $routeName = "courses/maa101/sets/xyz123";

	print "Testing POST /$routeName  \n";

	$url = $url_head . "$routeName";

	my $params4 = {%$params};

	$params4->{open_date} = time;


	$res = $furl->request(method=>'POST',url=>$url,content=>$params4);

	die $res->status_line unless $res->is_success;
	print $res->content;

}

## test #5

# update problem set xyz123


if ("5" ~~ @ARGV){

	my $routeName = "courses/maa101/sets/xyz123";

	print "Testing PUT /$routeName  \n";

	$url = $url_head . "$routeName";

	my $params4 = {%$params};

	$params4->{open_date} = time+24*60*60;


	$res = $furl->request(method=>'PUT',url=>$url,content=>$params4);

	die $res->status_line unless $res->is_success;
	print $res->content;

}






