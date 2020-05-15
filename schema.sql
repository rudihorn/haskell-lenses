
CREATE TABLE public.albums (
    album character varying(50) NOT NULL,
    quantity integer NOT NULL
);


CREATE TABLE public.tracks (
    track character varying(50) NOT NULL,
    date integer NOT NULL,
    rating integer NOT NULL,
    album character varying(50) NOT NULL
);


